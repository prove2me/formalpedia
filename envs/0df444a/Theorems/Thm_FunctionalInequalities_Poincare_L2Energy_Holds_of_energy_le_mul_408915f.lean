-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_L2Energy_Holds_of_energy_le_mul_408915f
-- name    : FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:32.360279+00:00
-- url     : https://prove2.me/theorems/b1f8874c-126b-4ccf-8836-be5f69157d55
-- title:
--   Transfer of Poincaré Bounds Through Energy Comparison
-- statement:
--   This is a comparison rule for extended-valued $L^2$ energies.
--
--   Let $\mu$ be a probability measure, let `source` and `target` be energy functionals on $L^2(\mu)$, and let $C,\kappa\in\mathbb{NNReal}$. Assume:
--
--   1. the source Poincaré inequality holds with constant $C$;
--   2. on every finite-energy target test $f$, the source energy is bounded by $\kappa$ times the target energy:
--   $$\mathrm{source}(f)\le \kappa\,\mathrm{target}(f).$$
--
--   Then the target Poincaré inequality holds with constant $\kappa C$:
--
--   $$\mathrm{Holds}_{\mu}(\mathrm{target},\kappa C).$$
--
--   The energies and their finite values are `ENNReal`-valued, so the comparison explicitly handles finite-energy domains, zero constants, and the possibility of infinite optimal constants.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/L2/Comparison.lean#L41-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.L2.Comparison`, declaration `FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Comparison
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
section
namespace FunctionalInequalities.Poincare.L2Energy
end FunctionalInequalities.Poincare.L2Energy
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.L2Energy
universe u
variable {α : Type u} [MeasurableSpace α]

theorem FunctionalInequalities.Poincare.L2Energy.Holds.of_energy_le_mul_408915f {μ : ProbabilityMeasure α}
    {source target : Energy.Functional (Lp ℝ 2 (μ : Measure α))} {C κ : NNReal}
    (hC : Holds μ source C)
    (henergy : ∀ f : target.domain,
      source f.1 ≤ (κ : ENNReal) * target f.1) :
    Holds μ target (κ * C) := by sorry
