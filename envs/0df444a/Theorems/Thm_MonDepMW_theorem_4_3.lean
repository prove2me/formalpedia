-- Prove2me | Theorems.Thm_MonDepMW_theorem_4_3
-- name    : MonDepMW.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:08.701013+00:00
-- url     : https://prove2.me/theorems/92029006-22e2-4981-ac09-7933d3c82039
-- title:
--   Theorem 4.3 — partition sequences of subpolynomial width
-- statement:
--   Let $r\geqslant1$ and let $\mathcal C$ be a monadically dependent graph class. There is a subpolynomial $k$ such that for every integer $q\geqslant2$ and $n$-vertex $G\in\mathcal C$ there is a sequence
--   $$\emptyset=B_m\subseteq B_{m-1}\subseteq\dots\subseteq B_1\subseteq B_0=V(G),\qquad m\leqslant1+\log_qn,$$
--   such that for every $i\in[m]$ and $u\in V(G)$, $\mathrm{Ball}^r_{\mathcal P_i}[u]$ intersects at most
--   $$k'(n)=q^r(\log_qn+1)\,k(n)$$
--   parts of $\mathcal P_{i-1}$, where $\mathcal P_i=\mathcal T_1(G,B_i)$. In particular $\mathcal P_0\sqsubseteq\dots\sqsubseteq\mathcal P_m$ is a partition sequence of radius-$r$ width at most $k'(n)$. Moreover, given $q,r,G$, such a sequence can be computed in $\widehat{\mathcal O}_{\mathcal C,r}(n^3)$ time.
--
--   This is the very concrete form of almost bounded partition merge-width, from which the goal theorem follows through Theorem 3.5.
--
--   **Formalization Note** The time bound is uniform in $q$. Input: $n$, the adjacency matrix, $q$, $r$. Output: $m$ and then the blocks of $B_0,\dots,B_m$.
--
--   Differences from the source:
--   - encoding: a graph class → GraphClass, members on each Fin n, no isomorphism closure; reason: every finite graph has a copy on some Fin n, and all quantities are isomorphism invariant
--   - encoding: Ô_{C,r}(n³) → (n+1)³·g(n) with g subpolynomial, chosen with the program before the instance; reason: Ô hides subpolynomial factors (p.11); n+1 only matters at n = 0, where n³·g(n) = 0 would forbid halting
--   - encoding: an algorithm on the RAM model with words of length O(log n) (App. C, p.43) → one program of the published word RAM, correct at every word size above b·(⌊log₂(n + inputs + 2)⌋+1), input in fixed cells, output read by a decoder of the output cells and n; reason: the paper names the model only; the layout is fixed once for all items and the decoders never see the input object
--   - encoding: partition sequence of radius-r width at most k′(n) → WidthLE with ⌊k′(n)⌋; reason: the width is an integer, so the two bounds are equivalent
--   - encoding: k : N → N with k(n) ⩽ subpoly(n) → k : ℕ → ℕ with Subpolynomial k; reason: a function bounded by a subpolynomial function is itself subpolynomial (squeeze), and conversely; N is the positive integers; the value at 0 is not constrained by the limit and enters only on the empty graph, where every bound holds, or not at all
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Theorem 4.3, p.16

import Mathlib
import Definitions.Def_TrulySubcubicAPSP_WordRAM
import Definitions.Def_MonDepMW_RunsWithin
import Definitions.Def_MonDepMW_decodeSet
import Definitions.Def_MonDepMW_Subpolynomial
import Definitions.Def_MonDepMW_MonadicallyDependent
import Definitions.Def_MonDepMW_IsDampingSequence

set_option autoImplicit false

open TrulySubcubicAPSP

namespace MonDepMW

/-- **Theorem 4.3.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.16: "Let r ∈ N and C be a monadically dependent graph class. Then there is a function k : N → N
with k(n) ⩽ subpoly_{C,r}(n) such that for any integer q ⩾ 2 and any n-vertex graph G ∈ C, there exists a sequence of vertex
subsets ∅ = Bm ⊆ Bm−1 ⊆ . . . ⊆ B1 ⊆ B0 = V (G) with m ⩽ 1 + log_q n satisfying the following condition. For every i ∈ [m]
and u ∈ V (G), Ball^r_{𝒫i}[u] intersects at most k′(n) := q^r · (log_q n + 1) · k(n) parts of 𝒫i−1, where 𝒫i := 𝒯1(G, Bi). In
particular, 𝒫0 ⊑ 𝒫1 ⊑ . . . ⊑ 𝒫m is a partition sequence for G of radius-r width at most k′(n). Moreover, given q, r, and G,
such a sequence B0, B1, . . . , Bm can be computed in Ô_{C,r}(n³) time."

**Formalization Note.** All three conclusions are in `IsDampingSequence` and in the run's specification. The time bound
`(n + 1)³ · g(n)` is uniform in `q`. Input: `n`, adjacency matrix, `q`, `r`. Output: `m`, then the `m + 1` blocks of `n` cells. -/
theorem theorem_4_3 (r : ℕ) (hr : 1 ≤ r) (𝒞 : GraphClass) (h𝒞 : MonadicallyDependent 𝒞) :
    ∃ k : ℕ → ℕ, Subpolynomial k ∧
      (∀ q : ℕ, 2 ≤ q → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n →
        ∃ (m : ℕ) (B : ℕ → Finset (Fin n)), IsDampingSequence G q r (k n) m B) ∧
      ∃ (P : List Instr) (b : ℕ) (g : ℕ → ℕ), Subpolynomial g ∧
        ∀ q : ℕ, 2 ≤ q → ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G ∈ 𝒞 n → ∀ W : ℕ,
          b * (Nat.log2 (n + q + r + 2) + 1) ≤ W →
          RunsWithin P W ((n + 1) ^ 3 * g n) (graphInput G ++ [(q : ℤ), (r : ℤ)]) fun out =>
            IsDampingSequence G q r (k n) (decodeSetSeq n out).1 (decodeSetSeq n out).2 := by sorry

end MonDepMW
