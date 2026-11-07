-- Prove2me | Theorems.Thm_MonDepMW_theorem_1_1
-- name    : MonDepMW.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:25.474194+00:00
-- url     : https://prove2.me/theorems/413cba00-0622-42f5-969d-b69ef5eb56d4
-- title:
--   Theorem 1.1 — monadically dependent classes have almost bounded merge-width
-- statement:
--   For every $r\geqslant1$ and monadically dependent graph class $\mathcal C$ there is a subpolynomial function $f$ such that for every $n$-vertex graph $G\in\mathcal C$, the radius-$r$ merge-width of $G$ is at most $f(n)$. Moreover, given $G\in\mathcal C$, a merge sequence for $G$ of radius-$r$ width at most $f(n)$ can be computed in $\widehat{\mathcal O}_{\mathcal C,r}(n^3)$ time.
--
--   This confirms the conjecture of Dreier and Toruńczyk that monadically dependent classes have almost bounded merge-width, and it is the combinatorial half of fixed-parameter first-order model checking on these classes.
--
--   **Formalization Note** Both clauses use the same $f$. The program may depend on $r$ and $\mathcal C$, but is one finite program for all members; the merge sequence is read from the output cells by a decoder that does not see $G$. Input: $n$, then the adjacency matrix.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: Ô_{C,r}(n³) → (n+1)³·g(n) with g subpolynomial, chosen with the program before the instance; reason: Ô hides subpolynomial factors (p.11); n+1 only matters at n = 0, where n³·g(n) = 0 would forbid halting
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
--   - encoding: a subpolynomial function f : N → N → f : ℕ → ℕ with Subpolynomial f; reason: N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 1.1, p.2 (restated p.17)

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_MergeSeq

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Theorem 1.1.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.2 (restated with its proof on p.17): "For every r ∈ N and monadically dependent graph class C, there
is a subpolynomial function f : N → N such that for every n-vertex graph G ∈ C, the radius-r merge-width of G is bounded by f(n).
Moreover, given G ∈ C, a merge sequence for G of radius-r width bounded by f(n) can be computed in Ô_{C,r}(n³) time."

**Formalization Note.** Both clauses, with the same `f`. `Ô_{C,r}(n³)` is `(n + 1)³ · g(n)`, `g` subpolynomial, chosen with the
program before `G`; `(n + 1)` only matters at `n = 0`. The program may depend on `r` and `𝒞`, but is a finite object, and it is correct
at every word size above `b · (⌊log₂(n + 2)⌋ + 1)` ("the RAM model with words of length O(log n)", p.43). Input: `n`, then the
adjacency matrix. The output is read by `decodeMergeSeq`, which sees only the output cells and `n`. -/
theorem theorem_1_1 (r : ℕ) (hr : 1 ≤ r) (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ f : ℕ → ℕ, Subpolynomial f ∧
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → MergeWidthLE G r (f n)) ∧
      ∃ (P : List Instr) (b : ℕ) (g : ℕ → ℕ), Subpolynomial g ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ W : ℕ, b * (Nat.log2 (n + 2) + 1) ≤ W →
          RunsWithin P W ((n + 1) ^ 3 * g n) (graphInput G) fun out =>
            (decodeMergeSeq n out).IsFor G ∧ (decodeMergeSeq n out).WidthLE r (f n) := by sorry

end MonDepMW
