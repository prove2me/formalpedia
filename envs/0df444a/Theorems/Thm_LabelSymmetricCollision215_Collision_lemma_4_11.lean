-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_lemma_4_11
-- name    : LabelSymmetricCollision215.Collision.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:01.960208+00:00
-- url     : https://prove2.me/theorems/367505e0-82d4-4519-b62a-720c7c426464
-- title:
--   Lemma 4.11 — Alternating projections
-- statement:
--   Assume $s\ge1$ and $N\ge2s$. With the spectral operator norm,
--   $$\|\Pi_{C_s^\perp}\Pi_{W^{\otimes s}}-\Pi_{C_s^\perp\cap W^{\otimes s}}\|^2=\|\Pi_{W^{\otimes s}}\Pi_{C_s^\perp}-\Pi_{C_s^\perp\cap W^{\otimes s}}\|^2\le\frac{2s-2}N.$$
--   For every $u$ orthogonal to the intersection,
--   $$\|\Pi_{C_s^\perp}\Pi_{W^{\otimes s}}u\|^2\le\frac{2s-2}N\|u\|^2.$$
--   This retains both product orders and the vector consequence, including $s=1$.
--
--   Differences from the source: none.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Lemma 4.11, PDF 27 / printed 25

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Lemma 4.11, PDF 27 / printed 25. -/
theorem lemma_4_11 (N s : ℕ) [NeZero N] (hs : 1 ≤ s) (hN : 2*s ≤ N) :
    ‖(freeTensor N s).starProjection.comp (wTensor N s).starProjection -
        (intersection N s).starProjection‖^2 = ‖projectionError N s‖^2 ∧
    ‖projectionError N s‖^2 ≤ (2*(s : ℝ)-2) / N ∧
    (∀ u : H (Tuple N s), u ∈ (intersection N s)ᗮ →
      ‖(freeTensor N s).starProjection ((wTensor N s).starProjection u)‖^2 ≤
        (2*(s : ℝ)-2) / N * ‖u‖^2) := by sorry

end LabelSymmetricCollision215.Collision
