-- Prove2me | Theorems.Thm_MinimaxInterventions1429_Separable_diameter_three_alignment
-- name    : MinimaxInterventions1429.Separable.diameter_three_alignment
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:19.231964+00:00
-- url     : https://prove2.me/theorems/94f9bb08-da4b-4e1a-b78b-d0af742e040a
-- title:
--   Lemma 3.4 — diameter-three alignment
-- statement:
--   Let $m,k\ge2$ and $L\in[0,1]^{m\times k}$, and write $a_g=L_{g1}$ and $\omega_{gh}=L_{gh}-L_{g1}$. Let a spanning tree of diameter at most three be rooted at $g_0$. Suppose $H,\kappa\ge0$, the child-parent edge estimates satisfy $|\widehat\Delta_{gr}-(a_g-a_r)|\le H$, and $|\widehat\omega_{gh}-\omega_{gh}|\le\kappa$ entrywise. Compute $\widehat a_{g_0}=0$ and $\widehat a_g=\widehat a_r+\widehat\Delta_{gr}$ along the rooted tree. Then
--
--   $$d_q(\widehat L,L)\le\tfrac32H+\kappa,\qquad
--   \widehat L_{gh}=\widehat a_g+\widehat\omega_{gh}.$$
--
--   The levels are calculated by the parent-path recurrence, rather than supplied as a correct reconstruction. This is the source's arbitrary-tree alignment statement; the specific anchor tree is constructed separately by the algorithm.
--
--   Differences from the source:
--   - encoding: rows and actions indexed from 1 with m,k ≥ 2 → Fin m and Fin k, source column 1 represented by 0, with explicit 2 ≤ m and 2 ≤ k; reason: order-preserving relabeling; closed-simplex mixtures and arbitrary real arrays retain every source instance
--   - encoding: minimum of F on the closed simplex and quotient distance defined by an infimum over scalar shifts → optimality compared against every simplex point and quotient distance equal to half the oscillation; reason: the finite nonempty simplex is compact and the objective continuous; Eq. (2) gives the identical quotient distance without default-valued infima
--   - generalization: H = 2(alpha + 2 kappa) + eta in Eq. (3) → any nonnegative edge-error bound H; reason: the tree proof uses only the edge-error and contrast-error bounds; Eq. (3) is a permitted instance
--   - encoding: a rooted spanning tree and levels defined by summing child-parent estimates → a parent map with a decreasing rank, graph paths of length at most three, and a computed parent-path sum; reason: each finite rooted tree admits this representation; no reconstruction bound is a tree field
-- source:
--   chaomeng chen, STOC 2027 submission #1429 (October 2026), Lemma 3.4, printed p.11 (PDF p.13)

import Definitions.Def_MinimaxInterventions1429_Separable_ObservationLaws
set_option autoImplicit false

namespace MinimaxInterventions1429.Separable

theorem diameter_three_alignment {m k : ℕ} [NeZero m] [NeZero k]
    (hm : 2 ≤ m) (hk : 2 ≤ k) (L w : Table m k) (hL : InCube L)
    (tree : ParentTree m) (hd : tree.diameterAtMostThree)
    (H κ : ℝ) (hH : 0 ≤ H) (hκ : 0 ≤ κ) (delta : Fin m → ℝ)
    (he : ∀ g, g ≠ tree.root → |delta g - (L g 0 - L (tree.parent g) 0)| ≤ H)
    (hw : ∀ g h, |w g h - contrasts L g h| ≤ κ) :
    quotientDist (fun g h => tree.levels delta g + w g h) L ≤ (3 : ℝ) / 2 * H + κ
    := by sorry

end MinimaxInterventions1429.Separable
