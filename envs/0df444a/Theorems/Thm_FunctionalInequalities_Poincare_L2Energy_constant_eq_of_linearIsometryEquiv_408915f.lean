-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_constant_eq_of_linearIsometryEquiv_408915f
-- name    : FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:26:25.044993+00:00
-- url     : https://prove2.me/theorems/b54804b9-f688-4a5a-bcc3-7bbe51295caf
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/L2/Energy.lean#L87-L135 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.L2.Energy`, declaration `FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
universe u
variable {α : Type u} [MeasurableSpace α]
section
namespace FunctionalInequalities.Poincare.L2Energy
end FunctionalInequalities.Poincare.L2Energy
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.L2Energy

theorem FunctionalInequalities.Poincare.L2Energy.constant_eq_of_linearIsometryEquiv_408915f {β : Type*} [MeasurableSpace β]
    (μ : ProbabilityMeasure α) (μ' : ProbabilityMeasure β)
    (energy : Energy.Functional (Lp ℝ 2 (μ : Measure α)))
    (energy' : Energy.Functional (Lp ℝ 2 (μ' : Measure β)))
    (e : Lp ℝ 2 (μ' : Measure β) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ : Measure α))
    (hvar : ∀ f, L2.variance μ (e f) = L2.variance μ' f)
    (henergy : ∀ f, energy' f = energy (e f)) :
    constant μ' energy' = constant μ energy := by sorry
