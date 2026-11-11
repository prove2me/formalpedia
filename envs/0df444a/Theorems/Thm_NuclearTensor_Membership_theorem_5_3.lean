-- Prove2me | Theorems.Thm_NuclearTensor_Membership_theorem_5_3
-- name    : NuclearTensor.Membership.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:38.049135+00:00
-- url     : https://prove2.me/theorems/322b11fe-90d6-4942-b856-8ed99d03c1ef
-- title:
--   Theorem 5.3 — polynomial-time nuclear-ball weak membership
-- statement:
--   For every $\eta>0$, there is a deterministic finite program for all positive dimensions $d$, positive orders $k$, and arbitrary real tensors $M\in(\mathbb R^d)^{\otimes k}$. Writing $K^*=\{Y:\|Y\|_*\le1\}$ for the exact real nuclear unit ball, it distinguishes
--   $$M\in K^*\qquad\text{from}\qquad\operatorname{dist}_F(M,K^*)\ge\eta.$$
--   It accepts every inside point and rejects every point at or beyond the Frobenius gap, including equality. In the open gap it may return either result, but it always terminates within the stated bound. There is no restriction on input norm, entries, rank, or growth of $k$.
--
--   For each fixed accuracy and fixed arithmetic/spectral cost convention, positive constants $B_\eta,C_\eta$ are chosen before $d,k,M$. The actual execution cost for $d\ge2$ is at most $B_\eta d^{C_\eta k}$. The scalar-input branch $d=1$ has constant cost; $k=1$ uses exact Euclidean-ball membership. The final program has no local service and no supplied procedures: the ball optimizer must be implemented in its own arithmetic code. Existence of the ordinary SVD interface is also asserted, preventing a vacuous computational model. This is the full headline target of the pinned submission.
--
--   Differences from the source:
--
--   - encoding: all real tensors with positive d and k → all row-major arrays for d,k>0, exact scalar/vector branches, and a constant scalar-input cost when d=1; reason: these are the same source inputs; neither d=1 nor k=1 is removed by the d>=2 assumption of Lemma 5.1
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
--   - encoding: the real signed finite-decomposition infimum and Frobenius distance → complete-lattice nonnegative extended-real infima, with Euclidean coordinate distance; reason: these have the same finite values in the source domain; empty domains are assigned infinity rather than a real default of zero
--   - encoding: time d^{O_eta(k)} → positive integer constants B_eta,C_eta chosen before d,k,M after the fixed spectral cost convention, with cost taken from finite executions; reason: integer upper bounds express the same asymptotic claim; no numerical exponent is fabricated and no constant can depend on the instance
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.21, Theorem 5.3; p.4, Theorem 1.1 informal alias

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem theorem_5_3 : Nonempty Spectral ∧
    ∀ η : ℝ, 0 < η → ∃ P : Program,
      ∀ (σ : Spectral) (A q : ℕ), 0 < A → 0 < q →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k →
      ∀ M : Tensor (List.replicate k d),
        runsWithin σ none A q [] P [d, k] ([η] ++ encodeVec M)
          (if d = 1 then (B : ℝ) else B * (d : ℝ) ^ (C * k))
          (fun s => ∃ b : Bool, outputsDecision s b ∧
            weakMembership (nuclearBall (List.replicate k d)) η M b ∧
            baseCaseDecision M b) := by sorry

end NuclearTensor.Membership
