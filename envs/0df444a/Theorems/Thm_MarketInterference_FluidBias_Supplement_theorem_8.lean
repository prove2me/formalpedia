-- Prove2me | Theorems.Thm_MarketInterference_FluidBias_Supplement_theorem_8
-- name    : MarketInterference.FluidBias.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:49:15.124727+00:00
-- url     : https://prove2.me/theorems/7afe0db0-ed99-4caa-88ef-59537db1f116
-- title:
--   Theorem 8 (companion theorem; not used in the proof of the goal) — uniform-fraction SP unbiasedness
-- statement:
--   Let $N$ be any finite capacitated matching network with nonnegative control, treatment and supply rates $\lambda,\lambda+\beta,\pi$. Draw the treatment fraction $\rho$ uniformly on $[0,1]$. For any optimal fluid dual selection $q^\rho$ whose scalar estimator $a^\rho\cdot\beta$ is measurable, with optimality holding almost everywhere, the fluid estimator is integrable and
--   $$
--   \mathbb E_\rho[a^\rho\cdot\beta]=\Delta.
--   $$
--   Also, for every real density $\tau>0$, first draw $\rho$ and then the conditional independent Poisson counts with means $(1-\rho)\lambda_i\tau$, $\rho(\lambda_i+\beta_i)\tau$ and $\pi_j\tau$. This joint law is a probability measure, its actual backward-difference SP estimator is integrable, and
--   $$
--   \mathbb E_{\rho,C,T,S}[\widehat\Delta^\tau_{SP}]=\Delta^\tau
--   =\Psi_\tau(1)-\Psi_\tau(0).
--   $$
--   These are the two regimes proved on p. 55. Neither needs sign consistency. The finite-sample identity concerns the source estimator itself, not a derivative chosen to define an unbiased replacement.
--
--   **Formalization Note** The dual is selected from the published program (5), and the finite prices are the published backward differences (18). Breakpoints with nonunique duals are retained; no uniqueness at every fraction, smoothness, curvature or variance assumption is added. At zero demand count the associated count contrast is zero. The mixture assigns zero estimator values at the two null fraction endpoints.
--
--   Differences from the source:
--   - encoding: finite source types and path sums → zero-based Fin types, finite arc types and finite-support path flows; reason: the same finite network and all of its supply-to-demand paths, including intermediate nodes
--   - reading: unbiasedness in expectation, with both regimes specified in the p. 55 proof → the fluid and every positive-real-density finite-sample identities, each with integrability; reason: the two conclusions are stated together and use the joint conditional-on-fraction law; null endpoints are assigned zero
--   - generalization: the named fluid optimal shadow prices under the standing uniqueness convention → any measurable scalar estimator from an almost-everywhere optimal dual selection; reason: optimal selections agree in the directional derivative almost everywhere; breakpoints remain allowed and the unique case is included
-- source:
--   Bright, Delarue and Lobel, Reducing Marketplace Interference Bias Via Shadow Prices, arXiv:2205.02274v4, p. 26, Theorem 8 and surrounding discussion; p. 55, proof; p. 25, (18)

import Mathlib
import Definitions.Def_MarketInterference_FluidBias_Supplement_UniformDesign

namespace MarketInterference.FluidBias.Supplement

open MeasureTheory

theorem theorem_8 {nd ns : ℕ} {I E : Type} [Fintype I] [Fintype E] [DecidableEq I]
    (N : Network nd ns I E) (lam beta : Fin nd → ℝ) (pi : Fin ns → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (htreat : ∀ i, 0 ≤ lam i + beta i) (hpi : ∀ j, 0 ≤ pi j)
    (q : ℝ → DualVar nd ns I E)
    (hqmeas : Measurable (fun ρ => spFluid (q ρ) beta))
    (hq : ∀ᵐ ρ ∂uniformFraction, IsOptimalDual N 1 (lam + ρ • beta) pi (q ρ)) :
    (Integrable (fun ρ => spFluid (q ρ) beta) uniformFraction ∧
      (∫ ρ, spFluid (q ρ) beta ∂uniformFraction) = Delta N lam beta pi) ∧
    ∀ τ : ℝ, 0 < τ →
      IsProbabilityMeasure (uniformExperimentLaw lam beta pi τ) ∧
      Integrable (mixedSP N τ) (uniformExperimentLaw lam beta pi τ) ∧
      (∫ z, mixedSP N τ z ∂uniformExperimentLaw lam beta pi τ) =
        MarketInterference.FiniteSample.PsiTau N lam beta pi τ 1 -
        MarketInterference.FiniteSample.PsiTau N lam beta pi τ 0 := by sorry

end MarketInterference.FluidBias.Supplement
