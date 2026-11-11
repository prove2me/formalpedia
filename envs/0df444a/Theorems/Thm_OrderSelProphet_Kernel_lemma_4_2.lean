-- Prove2me | Theorems.Thm_OrderSelProphet_Kernel_lemma_4_2
-- name    : OrderSelProphet.Kernel.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:57:29.765939+00:00
-- url     : https://prove2.me/theorems/c744a773-96fe-44ae-ae8c-72caab30cc2b
-- title:
--   Lemma 4.2 — integration by parts: $\ell_\Gamma(K,\lambda)=\Gamma(1-y(0))+\Gamma^2\int_0^1S_\lambda(1-y)(1-B')/S^2\,dt$
-- statement:
--   Let $\Gamma\in(0,1)$, $K$ an allocation kernel and $\lambda\in\Lambda$. Abbreviate $B=B_{K,\lambda}$, $y=y_{K,\lambda}$ and $S_\lambda=S_{K,\lambda}$. Then
--   $$\ell_\Gamma(K,\lambda)=\Gamma\big(1-y(0)\big)+\Gamma^2\int_0^1\frac{S_\lambda(t)(1-y(t))(1-B'(t))}{S(t)^2}\,dt,\quad(22)$$
--   with $S(t)=1-\Gamma t$; here $B'$ is defined almost everywhere.
--
--   Differences from the source:
--   - encoding: Λ: measurable λ : [0,1] → [0,1], identified when equal a.e. → Profile: measurable functions ℝ → ℝ with values in [0,1] on [0,1]; quantifying over representatives; reason: every quantity depends only on the a.e. class on [0,1]; a measurable function on [0,1] extends measurably to ℝ
--   - encoding: ℓ_Γ(K,λ) = Γ(1 − y(0)) + Γ² ∫_0^1 … → loadK Γ K λ = ENNReal.ofReal(Γ(1 − y(0)) + Γ² ∫_0^1 …); reason: the load is in ℝ≥0∞; the right side is a nonnegative real
--   - encoding: B′ defined almost everywhere → Lean's deriv B (0 where B is not differentiable); reason: B is 1-Lipschitz, so it is differentiable off a null set and the integral is unchanged
--   - encoding: Γ ∈ (0,1) and K ∈ 𝒦 fixed (§4.1, p. 12) → hypotheses Γ ∈ Ioo 0 1 and IsAllocationKernel K; reason: the section's standing assumptions
-- source:
--   Peng and Tang, Order-selection Prophet Inequality (Almost) Goes I.I.D., arXiv:2610.34892 (held file SHA-256 2f111b85…22dd), Lemma 4.2, p. 13

import Mathlib
import Definitions.Def_OrderSelProphet_Kernel_Profiles

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace OrderSelProphet.Kernel

/-- Lemma 4.2 (Integration by parts), p. 13. -/
theorem lemma_4_2 {Γ : ℝ} (hΓ : Γ ∈ Ioo (0 : ℝ) 1) (K : ℝ → ℝ → ℝ) (hK : IsAllocationKernel K)
    (lam : Profile) :
    loadK Γ K lam.1 = ENNReal.ofReal (Γ * (1 - yK K lam.1 0) + Γ ^ 2 * ∫ t in (0 : ℝ)..1,
      SK Γ K lam.1 t * (1 - yK K lam.1 t) * (1 - deriv (allocK K lam.1) t) / (1 - Γ * t) ^ 2) := by sorry

end OrderSelProphet.Kernel
