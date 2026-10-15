-- Prove2me | Theorems.Thm_MIPRE_Cost_compressibility_criterion_halting
-- name    : MIPRE.Cost.compressibility_criterion_halting
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:44.400323+00:00
-- url     : https://prove2.me/theorems/e69bd497-8c6c-4a1a-bc7a-958c702d5b5d
-- title:
--   Compressibility criterion against Mathlib's halting problem: a computable reduction on partial recursive codes
-- statement:
--   Throughout, computation is in the ambient cost model of the formalization: programs (`Prog`) form a small first-order language on binary-tree data (`Data`), $\mathrm{size}$ counts the nodes of a value, a bit string $x \in \{0,1\}^*$, a natural number (in binary) or a pair is a value through a size-faithful encoding $\mathrm{encode}$, and a program is its own tree encoding, of size $|e|$. The timed semantics charges one unit per evaluation rule plus the size of every value read, so a run of cost $t$ has output of size at most $t$. A polynomial-time computable function (`PolyTimeFun α β`) is a function together with a closed program computing it on encodings and an explicit polynomial bounding the cost in the size of the encoded input. "$e$ halts on the empty input" means that the program $e$, run on the value `nil`, halts (`Halts e nil`). The pair $(c, m)$ of a program and a parameter is a succinct description of $x \in \{0,1\}^*$ (`IsSuccinctDesc c m x`) when $c$ is closed, $|x| \le 2^m$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ answers the bit query, returning the $k$-th bit of $x$ if $k < |x|$ and the marker $2$ otherwise, within cost $(m+1)(\ell(k)+1)^2$, where $\ell(k)$ denotes the binary length of $k$. Mathlib's `Nat.Partrec.Code` is a Gödel numbering of the partial recursive functions: a code $\mathtt{pc}$ denotes the partial function $\mathtt{pc}.\mathrm{eval} : \mathbb{N} \to \mathrm{Part}\,\mathbb{N}$, and $(\mathtt{pc}.\mathrm{eval}\ 0).\mathrm{Dom}$ says that $\mathtt{pc}$ halts on the input $0$; $\mathrm{Computable}$ is Mathlib's computability of total functions between primcodable types (here codes and bit strings `List Bool`).
--
--   Let $A, B \subseteq \{0,1\}^*$ with distinguished strings $y_{\mathrm{yes}} \in A$ and $y_{\mathrm{no}} \in B$; let $S$ be a closed program with $S$ halting on $\mathrm{encode}(x)$ if and only if $x \notin B$; and let $\mathrm{Compr}$ be a polynomial-time computable compression procedure on claimed succinct descriptions $(c, m)$ with target parameter $n$ such that whenever $(c, m)$ genuinely describes $x$: $x \in A \Rightarrow \mathrm{Compr}((c,m),n) \in A$ and $x \in B \Rightarrow \mathrm{Compr}((c,m),n) \in B$ — the hypotheses of the compressibility criterion. Then there is a computable $g : \mathrm{Nat.Partrec.Code} \to \{0,1\}^*$ such that
--
--   $$ \forall \mathtt{pc}:\qquad \bigl((\mathtt{pc}.\mathrm{eval}\ 0)\ \text{is defined} \Rightarrow g(\mathtt{pc}) \in A\bigr)\ \wedge\ \bigl((\mathtt{pc}.\mathrm{eval}\ 0)\ \text{is undefined} \Rightarrow g(\mathtt{pc}) \in B\bigr). $$
--
--   This is Lin's compressibility criterion repackaged against the halting problem in the ambient formalization's own form (blueprint `lem:halting-form`): a Mathlib-computable reduction on codes of partial recursive functions, halting being halting of the code on input $0$. It is the seam at which the development meets Mathlib's computability, in the abstract form of the main theorem's halting reduction ($A$ and $B$ standing for normal-form-verifier games having a perfect PCC strategy, respectively value at most $\tfrac12$); the formalization's headline halting reduction is proved through the gap-compression instantiation of the per-level criterion.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.compressibility_criterion_halting`, with the hypotheses of `compressibility_criterion` (`hS` an equivalence, `Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr`) and the conclusion `∃ g : Nat.Partrec.Code → BitStr, Computable g ∧ ∀ pc, ((pc.eval 0).Dom → g pc ∈ A) ∧ (¬(pc.eval 0).Dom → g pc ∈ B)`. Only the interface changes: the reduction of `compressibility_criterion` is composed with the compiler `exists_compile` from codes to programs of the cost model, computable on descriptions and preserving halting on the empty input; the compiler carries no time bound, so the conclusion is `Computable` rather than polynomial-time. The departures from the paper recorded for the compression lemmas (the succinctness bound $(n+1)(\ell(k)+1)^2$, the next level $2n+1$, the explicit threshold $2^{K+1+|e|}$, the start level carried as data) apply unchanged.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L912-L933; blueprint lem:halting-form, https://vidick.github.io/MIPRE-formalization/blueprint/; corollary of [Lin25] J. Lin, MIP^co = coRE, Proc. 58th STOC, 2026, arXiv:2510.07162's compression criterion for RE-complete problems (in the formulation of [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript), restated against Mathlib's halting problem

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression

open MIPRE
open MIPRE.Cost
open Polynomial

theorem MIPRE.Cost.compressibility_criterion_halting
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → g pc ∈ B) := by sorry
