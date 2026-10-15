-- Prove2me | Theorems.Thm_MIPRE_Cost_recursive_compression_halting
-- name    : MIPRE.Cost.recursive_compression_halting
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:32.891034+00:00
-- url     : https://prove2.me/theorems/1745fe1d-8a35-447b-a469-1ea57ffa6842
-- title:
--   Recursive compression against Mathlib's halting problem: a computable reduction on partial recursive codes
-- statement:
--   Throughout, computation is in the ambient cost model of the formalization: programs (`Prog`) form a small first-order language on binary-tree data (`Data`), $\mathrm{size}$ counts the nodes of a value, a bit string $x \in \{0,1\}^*$, a natural number (in binary) or a pair is a value through a size-faithful encoding $\mathrm{encode}$, and a program is its own tree encoding, of size $|e|$. The timed semantics charges one unit per evaluation rule plus the size of every value read, so a run of cost $t$ has output of size at most $t$. A polynomial-time computable function (`PolyTimeFun α β`) is a function together with a closed program computing it on encodings and an explicit polynomial bounding the cost in the size of the encoded input. "$e$ halts on the empty input" means that the program $e$, run on the value `nil`, halts (`Halts e nil`). The pair $(c, m)$ of a program and a parameter is a succinct description of $x \in \{0,1\}^*$ (`IsSuccinctDesc c m x`) when $c$ is closed, $|x| \le 2^m$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ answers the bit query, returning the $k$-th bit of $x$ if $k < |x|$ and the marker $2$ otherwise, within cost $(m+1)(\ell(k)+1)^2$, where $\ell(k)$ denotes the binary length of $k$. Mathlib's `Nat.Partrec.Code` is a Gödel numbering of the partial recursive functions: a code $\mathtt{pc}$ denotes the partial function $\mathtt{pc}.\mathrm{eval} : \mathbb{N} \to \mathrm{Part}\,\mathbb{N}$, and $(\mathtt{pc}.\mathrm{eval}\ 0).\mathrm{Dom}$ says that $\mathtt{pc}$ halts on the input $0$; $\mathrm{Computable}$ is Mathlib's computability of total functions between primcodable types (here codes and bit strings `List Bool`).
--
--   Let $f : \{0,1\}^* \to \mathbb{N} \cup \{\infty\}$, let $A \subseteq \{0,1\}^*$ with a distinguished $y_0 \in A$ and $f(x) < \infty$ for all $x \in A$, and let $\mathrm{Compr}$ be a polynomial-time computable compression procedure on claimed succinct descriptions $(c, m)$ with target parameter $n$ such that whenever $(c, m)$ genuinely describes $x$: $f(\mathrm{Compr}((c,m),n)) \ge \max\{f(x), n\}$ and $x \in A \Rightarrow \mathrm{Compr}((c,m),n) \in A$ — the hypotheses of the recursive compression lemma. Then there is a computable $g : \mathrm{Nat.Partrec.Code} \to \{0,1\}^*$ such that
--
--   $$ \forall \mathtt{pc}:\qquad \bigl((\mathtt{pc}.\mathrm{eval}\ 0)\ \text{is defined} \Rightarrow g(\mathtt{pc}) \in A\bigr)\ \wedge\ \bigl((\mathtt{pc}.\mathrm{eval}\ 0)\ \text{is undefined} \Rightarrow f(g(\mathtt{pc})) = \infty\bigr). $$
--
--   This is the recursive compression lemma repackaged against the halting problem in the ambient formalization's own form (blueprint `lem:halting-form`): the reduction is presented as a Mathlib-computable map on codes of partial recursive functions, halting being halting of the code on input $0$, rather than on programs of the cost model. It is the seam at which the development meets Mathlib's computability, in the abstract form of the entanglement route of the main theorem ($A$ and $f$ standing for normal-form-verifier games and the entanglement requirement); the formalization's headline halting reduction is proved through the value-form route instead.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.recursive_compression_halting`, with the same hypotheses as `recursive_compression` and the conclusion `∃ g : Nat.Partrec.Code → BitStr, Computable g ∧ ∀ pc, ((pc.eval 0).Dom → g pc ∈ A) ∧ (¬(pc.eval 0).Dom → f (g pc) = ⊤)`. Only the interface changes: the reduction of `recursive_compression` is composed with a compiler from codes to programs of the cost model (`exists_compile`) that is computable on descriptions and preserves halting on the empty input; the compiler carries no time bound, so the conclusion is `Computable`, not polynomial-time. The departures from the paper recorded for `recursive_compression` (the succinctness bound $(n+1)(\ell(k)+1)^2$, the next level $2n+1$, the explicit threshold $2^{K+1+|e|}$) apply unchanged, as does the fact that the finiteness hypothesis on $f$ over $A$ is not used.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L888-L910; blueprint lem:halting-form, https://vidick.github.io/MIPRE-formalization/blueprint/; corollary of [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 5.1, restated against Mathlib's halting problem

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

theorem MIPRE.Cost.recursive_compression_halting
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : Nat.Partrec.Code → BitStr, Computable g ∧
      ∀ pc : Nat.Partrec.Code,
        ((pc.eval 0).Dom → g pc ∈ A) ∧
        (¬(pc.eval 0).Dom → f (g pc) = ⊤) := by sorry
