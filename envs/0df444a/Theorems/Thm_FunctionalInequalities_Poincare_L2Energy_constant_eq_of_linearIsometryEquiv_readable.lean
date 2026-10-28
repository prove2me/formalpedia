-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_constant_eq_of_linearIsometryEquiv_readable
-- name    : FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:24.398683+00:00
-- url     : https://prove2.me/theorems/6ef866fb-b080-4fd9-8723-b37080782c4a
-- title:
--   Poincaré Constants Under Isometric Energy Equivalence
-- statement:
--   This is an invariance principle for optimal extended-energy Poincaré constants.
--
--   Let $\mu$ and $\mu'$ be probability measures on measurable spaces $\alpha$ and $\beta$. Let `energy` and `energy'` be extended-valued energy functionals on the corresponding real $L^2$ spaces, and let $e:L^2(\mu')\simeq L^2(\mu)$ be a real linear isometric equivalence. Assume that for every $f$, variance is preserved:
--   $$\operatorname{Var}_{\mu}(ef)=\operatorname{Var}_{\mu'}(f),$$
--   and that the energies intertwine:
--   $$\mathrm{energy}'(f)=\mathrm{energy}(ef).$$
--   Then their optimal Poincaré constants are equal:
--
--   $$C_P(\mu,\mathrm{energy})=C_P(\mu',\mathrm{energy}').$$
--
--   The functionals may take the value $\infty$; the statement compares exactly the finite-energy domains and does not assume closedness, quadraticity, or a Markov property.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.L2Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem constant_eq_of_linearIsometryEquiv {β : Type*} [MeasurableSpace β]
--       (μ : ProbabilityMeasure α) (μ' : ProbabilityMeasure β)
--       (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
--       (energy' : Energy.Functional (Lp ℝ 2 (μ' : Measure β)))
--       (e : Lp ℝ 2 (μ' : Measure β) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ : Measure α))
--       (hvar : ∀ f, L2.variance μ (e f) = L2.variance μ' f)
--       (henergy : ∀ f, energy' f = energy (e f)) :
--       constant μ' energy' = constant μ energy
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   [Source excerpt, lines 89–96](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/L2/Energy.lean#L89-L96) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/L2/Energy.lean#L87-L135 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.L2.Energy`, declaration `FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_L2_Energy

open MeasureTheory
universe u
variable {α : Type u} [MeasurableSpace α]

theorem FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_readable {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (μ' : ProbabilityMeasure β)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (energy' : Energy.Functional (Lp ℝ 2 (μ' : Measure β)))
    (e : Lp ℝ 2 (μ' : Measure β) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ : Measure α))
    (hvar : ∀ f, L2.variance μ (e f) = L2.variance μ' f)
    (henergy : ∀ f, energy' f = energy (e f)) :
    constant μ' energy' = constant μ energy := by sorry
