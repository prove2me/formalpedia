-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_corollary_4_16
-- name    : LabelSymmetricCollision215.Collision.corollary_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:12.426044+00:00
-- url     : https://prove2.me/theorems/e51fa5f8-2d76-4153-b669-b1abdfa4f4ca
-- title:
--   Corollary 4.16 — Weighted occupancy
-- statement:
--   Assume $N\ge9$, $S\ge\log_2N$, integer $0\le t\le\sqrt N$, a possibly unnormalized vector $\phi$ in the compression image, support on at most $t$ occupied cells, and orbit-span dimension at most $2^S$ for every algorithm-basis projection. Then
--   $$\sum_{s=0}^t s\|\Pi_{=0}\Lambda_s\phi\|^2\le\min\{t,2S/\log_2N\}\|\phi\|^2.$$
--   This retains all inherited hypotheses, the weight $s$, and the norm factor.
--
--   Differences from the source:
--   - encoding: database vectors, support, tensor norms and log₂N → finite complex Euclidean coordinates, real dimension charge S and log N / log 2; reason: the vector result uses S solely in the displayed real inequalities and orbit dimension bound; no algorithm or progress estimate is assumed
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Corollary 4.16, PDF 32 / printed 30

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Corollary 4.16, PDF 32 / printed 30. -/
theorem corollary_4_16 {M N : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (S : ℝ) (hN : 9 ≤ N) (hS : logTwo N ≤ S)
    (t : ℕ) (ht : (t : ℝ) ≤ Real.sqrt N)
    (φ : H (Reg M N W × DB M N))
    (hcomp : compressedProjection M N W φ = φ)
    (hsupp : SupportedAtMost t φ) (horbit : OrbitBound S φ) :
    (∑ s ∈ Finset.range (t+1), (s : ℝ) *
      ‖freeProjection M N W (occupancyProjection M N W s φ)‖^2) ≤
      min (t : ℝ) (2*S/logTwo N) * ‖φ‖^2 := by sorry

end LabelSymmetricCollision215.Collision
