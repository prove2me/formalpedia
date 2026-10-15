-- Prove2me | Theorems.Thm_MIPRE_Cost_recursive_compression
-- name    : MIPRE.Cost.recursive_compression
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:26:33.522496+00:00
-- url     : https://prove2.me/theorems/347236a4-0cf5-4f17-a875-e63d838001f3
-- title:
--   Recursive compression: a compressor for succinct descriptions yields a reduction from the halting problem
-- statement:
--   Throughout, computation is in the ambient cost model of the formalization: programs (`Prog`) form a small first-order language on binary-tree data (`Data`), $\mathrm{size}$ counts the nodes of a value, a bit string $x \in \{0,1\}^*$, a natural number (in binary) or a pair is a value through a size-faithful encoding $\mathrm{encode}$, and a program is its own tree encoding, of size $|e|$. The timed semantics charges one unit per evaluation rule plus the size of every value read, so a run of cost $t$ has output of size at most $t$. A polynomial-time computable function (`PolyTimeFun α β`) is a function together with a closed program computing it on encodings and an explicit polynomial bounding the cost in the size of the encoded input. "$e$ halts on the empty input" means that the program $e$, run on the value `nil`, halts (`Halts e nil`). The pair $(c, m)$ of a program and a parameter is a succinct description of $x \in \{0,1\}^*$ (`IsSuccinctDesc c m x`) when $c$ is closed, $|x| \le 2^m$, and for every $k \in \mathbb{N}$ the program $c$ on the binary input $k$ answers the bit query, returning the $k$-th bit of $x$ if $k < |x|$ and the marker $2$ otherwise, within cost $(m+1)(\ell(k)+1)^2$, where $\ell(k)$ denotes the binary length of $k$.
--
--   Let $f : \{0,1\}^* \to \mathbb{N} \cup \{\infty\}$ be any function and $A \subseteq \{0,1\}^*$ a language, with:
--
--   1. a distinguished element $y_0 \in A$;
--   2. $f(x) < \infty$ for every $x \in A$;
--   3. a polynomial-time computable compression procedure $\mathrm{Compr}$, taking a claimed succinct description $(c, m)$ and a target parameter $n \in \mathbb{N}$ to a string $\mathrm{Compr}((c,m),n) \in \{0,1\}^*$, such that whenever $(c, m)$ is a genuine succinct description of some $x$: (a) $f(\mathrm{Compr}((c,m),n)) \ge \max\{f(x), n\}$, and (b) if $x \in A$ then $\mathrm{Compr}((c,m),n) \in A$.
--
--   Then there is a polynomial-time computable $g : \mathrm{Prog} \to \{0,1\}^*$ reducing the halting problem to $A$:
--
--   $$ \forall e \in \mathrm{Prog}:\qquad \bigl(e \text{ halts on the empty input} \Rightarrow g(e) \in A\bigr)\ \wedge\ \bigl(e \text{ does not halt on the empty input} \Rightarrow f(g(e)) = \infty\bigr). $$
--
--   Nothing is assumed about the computability of $f$, nor about the output of $\mathrm{Compr}$ on inputs that are not genuine succinct descriptions, but $\mathrm{Compr}$ must be total and polynomial-time everywhere ([MNY, §7] shows this is essential). This is the entire self-referential part of the proof of $\mathrm{MIP}^* = \mathrm{RE}$, isolated as a statement with no quantum content: in the entanglement-form route, $A$ is the set of normal-form verifiers with a perfect strategy and finite entanglement requirement, $f$ the entanglement requirement $\mathrm{Ent}(\cdot, \tfrac12)$, and $\mathrm{Compr}$ the compression theorem for games. Its halting-problem form against Mathlib's `Nat.Partrec.Code` is `recursive_compression_halting`; the value-form pipeline of the formalization uses Lin's compressibility criterion instead.
--
--   **Formalization Note**. The statement is `MIPRE.Cost.recursive_compression`, with $f$ of type `BitStr → ℕ∞`, `Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr`, `IsSuccinctDesc c m x` as above, and the conclusion `∃ g : PolyTimeFun Prog BitStr, ∀ e, (Halts e .nil → g e ∈ A) ∧ (¬ Halts e .nil → f (g e) = ⊤)`; the halting problem is that of the ambient model's programs on the input `nil`. The finiteness hypothesis $f(x) < \infty$ on $A$ is part of the statement of [MNY] (it makes the two conclusions exclusive) but is not used by the proof, which is why it is named `_hA`. Three departures from the paper's statement and proof are recorded in the module docstring of `MIPRE/Foundations/Compression.lean`. (i) *Succinctness time bound*: [MNY, Definition 2.4] requires the runtime of the description on every query $k$ to be at most $n$; in a model that charges for reading its input this is vacuous for $\ell(k) > n$, so the formalization requires $(n+1)(\ell(k)+1)^2$ instead, the quadratic factor in $\ell(k)$ being what the bit-indexing program `bitAtProg` achieves (each zero test and decrement of the binary index copies it); any fixed polynomial in $n$ and $\ell(k)$ would do, provided the compression theorem for games uses the same one. (ii) *The next level is $2n+1$, not $n+1$*: incrementing a binary numeral needs a carry propagation, prepending a one bit is a single node (`PolyTimeFun.next`); the levels $n, 2n+1, 4n+3, \dots$ still grow without bound and $\ell(2n+1) = \ell(n)+1$ keeps every overhead polynomial in $|e| + \ell(n)$. (iii) *The threshold is explicit*: $r(e) = 2^{K+1+|e|}$ for a constant $K$ obtained from the overhead polynomial by the threshold lemma `exists_threshold` (above it, a polynomial in $|e| + \ell(n)$ is at most $n+1$), and it is computed in polynomial time by `PolyTimeFun.threshold K`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Compression.lean#L119-L288; blueprint lem:recursive-compression, https://vidick.github.io/MIPRE-formalization/blueprint/; [MNY] A. Marks, S. S. Nezhadi, H. Yuen, The recursive compression method for proving undecidability results, manuscript, Lemma 5.1

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

theorem MIPRE.Cost.recursive_compression
    (f : BitStr → ℕ∞) (A : Set BitStr)
    (y₀ : BitStr) (hy₀ : y₀ ∈ A)
    (_hA : ∀ x ∈ A, f x < ⊤)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (max (f x) (n : ℕ∞) ≤ f (Compr ((c, m), n))) ∧
        (x ∈ A → Compr ((c, m), n) ∈ A)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → f (g e) = ⊤) := by sorry
