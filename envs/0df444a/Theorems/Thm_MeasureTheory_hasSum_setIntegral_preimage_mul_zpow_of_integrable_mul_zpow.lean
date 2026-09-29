-- Prove2me | Theorems.Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
-- name    : MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/eb189f53-d349-52cc-8b10-23de23b69ca0
-- title:
--   Shell decomposition of an integral with integer exponent
-- statement:
--   Let $\Omega$ be a measurable space carrying a measure $\rho$, let $E\colon\Omega\to\mathbb{Z}$ be measurable, let $G\colon\Omega\to\mathbb{C}$ be an arbitrary function, and let $r$ be a real number with $0<r$ such that $\omega\mapsto G(\omega)\,(r:\mathbb{C})^{E(\omega)}$ is $\rho$-integrable (integer powers throughout, so negative exponents are inverses). The conclusion is a conjunction of three assertions. First, the family indexed by $n\in\mathbb{Z}$ whose $n$-th term is $\bigl(\int_{E^{-1}(\{n\})}\|G\|\,d\rho\bigr)\,r^{n}$ has sum (in the unconditional `HasSum` sense over $\mathbb{Z}$) equal to $\int_\Omega \|G(\omega)\|\,r^{E(\omega)}\,d\rho$. Second, the family $n\mapsto \bigl\|\int_{E^{-1}(\{n\})}G\,d\rho\bigr\|\,r^{n}$ is summable. Third, for every $Y\in\mathbb{C}$ with $\|Y\|=r$, the function $\omega\mapsto G(\omega)\,Y^{E(\omega)}$ is $\rho$-integrable and the family $n\mapsto\bigl(\int_{E^{-1}(\{n\})}G\,d\rho\bigr)\,Y^{n}$ has sum $\int_\Omega G(\omega)\,Y^{E(\omega)}\,d\rho$. Bochner integrals of non-integrable functions are $0$ by convention, but the integrability hypothesis is exactly what makes all three clauses substantive.
--
--   This is the dictionary converting an integral weighted by $Y^{E}$ into a Laurent series in $Y$ whose coefficients are the integrals of $G$ over the level sets (shells) of the integer-valued exponent $E$, with absolute convergence on the whole circle $\|Y\|=r$ determined by integrability at the single value $Y=r$. It is used by the results on evaluating such integrals against power series, namely [`MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq`](thm.html#MeasureTheory.exists_hasSum_mul_zpow_eval_mul_integral_prod_of_ae_forall_integral_mul_zpow_mul_eval_eq) and [`MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq`](thm.html#MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
    {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) (E : Ω → ℤ) (hE : Measurable E)
    (G : Ω → ℂ) {r : ℝ} (hr : 0 < r)
    (hG : Integrable (fun ω => G ω * (r : ℂ) ^ E ω) ρ) :
    HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, ‖G ω‖ ∂ρ) * r ^ n) (∫ ω, ‖G ω‖ * r ^ E ω ∂ρ) ∧
    (Summable fun n : ℤ => ‖∫ ω in E ⁻¹' {n}, G ω ∂ρ‖ * r ^ n) ∧
    ∀ Y : ℂ, ‖Y‖ = r →
      Integrable (fun ω => G ω * Y ^ E ω) ρ ∧
      HasSum (fun n : ℤ => (∫ ω in E ⁻¹' {n}, G ω ∂ρ) * Y ^ n) (∫ ω, G ω * Y ^ E ω ∂ρ) := by sorry
