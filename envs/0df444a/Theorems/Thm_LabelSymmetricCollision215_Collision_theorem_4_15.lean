-- Prove2me | Theorems.Thm_LabelSymmetricCollision215_Collision_theorem_4_15
-- name    : LabelSymmetricCollision215.Collision.theorem_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:54.654202+00:00
-- url     : https://prove2.me/theorems/6927bc24-9188-4754-88d2-d30bf841bad8
-- title:
--   Theorem 4.15 — Space bounds for collision-free database states
-- statement:
--   Assume $N\ge9$, $S\ge\log_2N$, and $0\le t\le\sqrt N$ is an integer. Let $\phi$ be any possibly unnormalized compressed joint vector supported on databases with at most $t$ occupied cells. Suppose each algorithm-basis projection of $\phi$ has label-orbit span dimension at most $2^S$. For every integer $0\le s\le t$,
--   $$\|\Pi_{=0}\Lambda_s\phi\|^2\le\begin{cases}\|\Lambda_s\phi\|^2,&s\le2S/\log_2N,\\\frac{2s-2}N\|\Lambda_s\phi\|^2,&s>2S/\log_2N.\end{cases}$$
--   This is the full two-regime vector bound, including the zero sector.
--
--   Differences from the source:
--   - encoding: database vectors, support, tensor norms and log₂N → finite complex Euclidean coordinates, real dimension charge S and log N / log 2; reason: the vector result uses S solely in the displayed real inequalities and orbit dimension bound; no algorithm or progress estimate is assumed
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, Theorem 4.15, PDF 31 / printed 29

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor

namespace LabelSymmetricCollision215.Collision

/-- Magniez–Zur, Theorem 4.15, PDF 31 / printed 29. -/
theorem theorem_4_15 {M N : ℕ} {W : Type} [Fintype W] [DecidableEq W] [NeZero N]
    (hM : 0 < M) (S : ℝ) (hN : 9 ≤ N) (hS : logTwo N ≤ S)
    (t : ℕ) (ht : (t : ℝ) ≤ Real.sqrt N)
    (φ : H (Reg M N W × DB M N))
    (hcomp : compressedProjection M N W φ = φ)
    (hsupp : SupportedAtMost t φ) (horbit : OrbitBound S φ) : ∀ s ≤ t,
    ‖freeProjection M N W (occupancyProjection M N W s φ)‖^2 ≤
      if (s : ℝ) ≤ 2*S/logTwo N then ‖occupancyProjection M N W s φ‖^2
      else (2*(s : ℝ)-2)/N * ‖occupancyProjection M N W s φ‖^2 := by sorry

end LabelSymmetricCollision215.Collision
