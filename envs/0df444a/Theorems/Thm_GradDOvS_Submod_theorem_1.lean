-- Prove2me | Theorems.Thm_GradDOvS_Submod_theorem_1
-- name    : GradDOvS.Submod.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:18:00.236639+00:00
-- url     : https://prove2.me/theorems/75c1f31a-2c0a-402d-9934-014eb7c69387
-- title:
--   Theorem 1, p. 19 (PGS part; n ≥ 32σ²/ε²·log(8d/δ) replications fixed in advance) — rounding an (ε/2, δ/2)-PGS point gives an (ε, δ)-PGS solution
-- statement:
--   Assume Assumption 1 with $\sigma > 0$, $d \ge 1$, $\epsilon > 0$ and $0 < \delta < 1$. Let $\bar x$ be a random point of $[0,1]^d$, measurable and independent of the rounding replications, which is an $(\epsilon/2,\delta/2)$-PGS solution of the relaxed problem (5):
--   $$\mathbb P\Big(\tilde f(\bar x) > \min_A f(A) + \frac\epsilon2\Big) \le \frac\delta2.$$
--   Run Algorithm 1 with $n$ replications at each neighbouring point $S^0,\dots,S^d$ of $\bar x$, where
--   $$n \ge \frac{32\sigma^2}{\epsilon^2}\log\frac{8d}{\delta}.$$
--   Then, whichever minimizer $S^i$ of the sample means $\hat F_n(S^0),\dots,\hat F_n(S^d)$ is returned,
--   $$\mathbb P\Big(f(S^i) > \min_A f(A) + \epsilon\Big) \le \delta,$$
--   i.e. Algorithm 1 returns an $(\epsilon,\delta)$-PGS solution of problem (1).
--
--   **Formalization Note** Algorithm 1 simulates "until the $1-\delta/(4d)$ confidence half-width of $\hat F_n(S^i)$ is smaller than $\epsilon/4$"; the proof (p. ec2) reads this as the fixed sample size $\frac{32}{\epsilon^2}\log\frac{8d}{\delta}$ per point, which is the formalized version, with the factor $\sigma^2$ restored (the printed count is for $\sigma = 1$). The cost bound of Theorem 1 is not formalized. Submodularity and Assumption 4 are not needed and not assumed. The failure probability is bounded for the event that *some* minimizer of the sample means is bad, so every tie-break is covered.
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 19, Theorem 1; proof p. ec1–ec2 (PDF 39–40) (sample size n, with σ² restored)

import Mathlib
import Definitions.Def_GradDOvS_Submod_Model

open MeasureTheory ProbabilityTheory

namespace GradDOvS.Submod

/-- Theorem 1, p. 19 (PGS part; `n ≥ 32σ²/ε² · log(8d/δ)` replications per neighbouring point fixed in
advance): if `x̄ ∈ [0,1]^d` is an `(ε/2, δ/2)`-PGS point of the Lovász extension, independent of
the rounding replications, then Algorithm 1 returns a point within `ε` of `min f` with probability
at least `1 - δ`, whatever minimizer of the sample means it selects. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] {d T n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Finset (Fin d) → ℝ) (σ : NNReal)
    (Z : Slot d T n → Ω → Finset (Fin d) → ℝ) (hZ : IsSimOracle P f σ Z)
    (hd : 1 ≤ d) (hσ : 0 < σ) (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (xbar : Ω → Fin d → ℝ) (hxm : Measurable xbar) (hxbox : ∀ ω, xbar ω ∈ box d)
    (hindep : IndepFun xbar (fun ω (p : Fin (d + 1) × Fin n) => Z (Sum.inr p) ω) P)
    (hpgs : P {ω | minf f + ε / 2 < lovasz f (xbar ω)} ≤ ENNReal.ofReal (δ / 2))
    (hn : 32 * (σ : ℝ) ^ 2 / ε ^ 2 * Real.log (8 * d / δ) ≤ n) :
    P (roundFail f ε Z xbar) ≤ ENNReal.ofReal δ := by sorry

end GradDOvS.Submod
