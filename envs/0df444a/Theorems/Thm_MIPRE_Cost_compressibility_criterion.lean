-- Prove2me | Theorems.Thm_MIPRE_Cost_compressibility_criterion
-- name    : MIPRE.Cost.compressibility_criterion
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:36.726+00:00
-- url     : https://prove2.me/theorems/8ffe1422-d401-4f2c-a58d-2e03a9c6d780
-- title:
--   Lin's compressibility criterion: a compressor preserving two classes yields a reduction from the halting problem
-- statement:
--   Throughout, computation is in the ambient cost model of the formalization: programs (`Prog`) form a small first-order language on binary-tree data (`Data`), $\mathrm{size}$ counts the nodes of a value, a bit string $x \in \{0,1\}^*$, a natural number (in binary) or a pair is a value through a size-faithful encoding $\mathrm{encode}$, and a program is its own tree encoding, of size $|e|$. The timed semantics charges one unit per evaluation rule plus the size of every value read, so a run of cost $t$ has output of size at most $t$. A polynomial-time computable function (`PolyTimeFun α β`) is a function together with a closed program computing it on encodings and an explicit polynomial bounding the cost in the size of the encoded input. "$e$ halts on the empty input" means that the program $e$, run on the value `nil`, halts (`Halts e nil`). The pair $(c, m)$ of a program and a parameter is a succinct description of $x \in \{0,1\}^*$ (`IsSuccinctDesc c m x`) when $c$ is closed, $|x| \le 2^m$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ answers the bit query, returning the $k$-th bit of $x$ if $k < |x|$ and the marker $2$ otherwise, within cost $(m+1)(\ell(k)+1)^2$, where $\ell(k)$ denotes the binary length of $k$.
--
--   Let $A, B \subseteq \{0,1\}^*$ be languages. Suppose:
--
--   1. there are distinguished strings $y_{\mathrm{yes}} \in A$ and $y_{\mathrm{no}} \in B$;
--   2. the complement of $B$ is recursively enumerable, witnessed by a closed program $S$ (well-scoped in one variable) with: $S$ halts on $\mathrm{encode}(x)$ if and only if $x \notin B$;
--   3. there is a polynomial-time computable compression procedure $\mathrm{Compr}$, taking a claimed succinct description $(c, m)$ and a target parameter $n \in \mathbb{N}$ to a string, such that whenever $(c, m)$ is a genuine succinct description of $x$: if $x \in A$ then $\mathrm{Compr}((c,m),n) \in A$, and if $x \in B$ then $\mathrm{Compr}((c,m),n) \in B$.
--
--   Then there is a polynomial-time computable $g : \mathrm{Prog} \to \{0,1\}^*$ reducing the halting problem to the pair $(A, B)$:
--
--   $$ \forall e \in \mathrm{Prog}:\qquad \bigl(e \text{ halts on the empty input} \Rightarrow g(e) \in A\bigr)\ \wedge\ \bigl(e \text{ does not halt on the empty input} \Rightarrow g(e) \in B\bigr). $$
--
--   This is Lin's compression criterion for $\mathrm{RE}$-complete problems (the direction "weakly compressible implies $\mathrm{RE}$-complete"), in the succinct-description formulation of Marks, Nezhadi and Yuen, and the level-free form of the lemma the formalization's main theorem uses: $A$ the normal-form verifiers with a perfect PCC strategy, $B$ those of value at most $\tfrac12$, $S$ the lower semidecider for the value. Compared with the recursive compression lemma, the growth hypothesis on a measure $f$ is replaced by a second preserved class whose complement is semidecidable. Its form against Mathlib's halting problem is `compressibility_criterion_halting`; the per-level form `compressibility_criterion_levels`, of which this is a special case, is the one an instantiation by gap-preserving compression can satisfy.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.compressibility_criterion`, with `Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr`, `hS : ∀ x, Halts S (encode x) ↔ x ∉ B` (an equivalence; both directions are used), and the conclusion `∃ g : PolyTimeFun Prog BitStr, ∀ e, (Halts e .nil → g e ∈ A) ∧ (¬ Halts e .nil → g e ∈ B)`, the halting problem being that of ambient programs on the input `nil`. It is derived from `compressibility_criterion_levels` with constant families, $n_0 = 0$, the semidecider precomposed with the first projection, and the compressor $(c, n) \mapsto \mathrm{Compr}((c, n), n)$; the extra hypotheses of the per-level form ($n \ge n_0$, $2|c| \le n$, $|x| \le n+1$, the levels) are simply dropped. Three departures from the paper's statement and proof are recorded in the module docstring of `MIPRE/Foundations/Compression.lean`. (i) *Succinctness time bound*: [MNY, Definition 2.4] requires the runtime of the description on every query $k$ to be at most $n$; in a model that charges for reading its input this is vacuous for $\ell(k) > n$, so the formalization requires $(n+1)(\ell(k)+1)^2$ instead, the quadratic factor in $\ell(k)$ being what the bit-indexing program `bitAtProg` achieves (each zero test and decrement of the binary index copies it); any fixed polynomial in $n$ and $\ell(k)$ would do, provided the compression theorem for games uses the same one. (ii) *The next level is $2n+1$, not $n+1$*: incrementing a binary numeral needs a carry propagation, prepending a one bit is a single node (`PolyTimeFun.next`); the levels $n, 2n+1, 4n+3, \dots$ still grow without bound and $\ell(2n+1) = \ell(n)+1$ keeps every overhead polynomial in $|e| + \ell(n)$. (iii) *The threshold is explicit*: $r(e) = 2^{K+1+|e|}$ for a constant $K$ obtained from the overhead polynomial by the threshold lemma `exists_threshold` (above it, a polynomial in $|e| + \ell(n)$ is at most $n+1$), and it is computed in polynomial time by `PolyTimeFun.threshold K`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L827-L875; blueprint lem:compressible-criterion, https://vidick.github.io/MIPRE-formalization/blueprint/; [Lin25] J. Lin, MIP^co = coRE, Proc. 58th STOC, 2026, arXiv:2510.07162, the compression criterion for RE-complete problems (direction "weakly compressible implies RE-complete"), in the succinct-description formulation of [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript

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

theorem MIPRE.Cost.compressibility_criterion
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → g e ∈ B) := by sorry
