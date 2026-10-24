-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_biconjugate_lowerTruncate_potentialIntegrable_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:35.633361+00:00
-- url     : https://prove2.me/theorems/4777742f-a43b-487c-bbdb-2c2ab135d711
-- title:
--   Integrability of the Truncated Biconjugate
-- statement:
--   This proves admissibility of the actual biconjugate of a lower truncation.
--
--   Let $\mu$ be a nonzero finite Borel measure on a real inner-product space, let $f:E\to\overline{\mathbb R}$ be potential-integrable, and let $M\in\mathbb R$. Then
--
--   $$
--   \operatorname{Leg}\!\left(\operatorname{Leg}(\max(f,-M))\right)
--   $$
--
--   is potential-integrable with respect to $\mu$. The statement includes the required Borel measurability and finite-measure assumptions and derives integrability from the truncation bounds rather than requiring it separately for the biconjugate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Integrability.lean#L68-L101 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Integrability`, declaration `FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Convexification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_408915f [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (legendre (legendre (lowerTruncate f M))) μ := by sorry
