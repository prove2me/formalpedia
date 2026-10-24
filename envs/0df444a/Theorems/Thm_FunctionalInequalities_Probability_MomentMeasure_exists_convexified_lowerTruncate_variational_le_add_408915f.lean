-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_convexified_lowerTruncate_variational_le_add_408915f
-- name    : FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:20:40.390185+00:00
-- url     : https://prove2.me/theorems/c1b095d1-69c0-4857-a7a5-716aac9b3bef
-- title:
--   Convexified Competitor Within Epsilon
-- statement:
--   This formalizes the epsilon reduction underlying Proposition 12 of Cordero–Erausquin–Klartag (arXiv:1304.0630v1).
--
--   Let $dx$ be a measure and let $\mu$ be a nonzero finite Borel measure on a real inner-product space. If $f$ is potential-integrable and $\varepsilon>0$, then there exists an integer $n>0$ such that, with
--
--   $$
--   c=\operatorname{Leg}\!\left(\operatorname{Leg}\left(\max(f,-n)\right)\right),
--   $$
--
--   $c$ is a convex lower-semicontinuous potential, is potential-integrable with respect to $\mu$, and
--
--   $$
--   \mathcal V_{dx,\mu}(f)
--   \leq
--   \mathcal V_{dx,\mu}(c)+\varepsilon.
--   $$
--
--   The variational functional and the epsilon are interpreted in `EReal`, so zero and infinite exponential masses remain part of the statement.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Truncation.lean#L184-L215 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Truncation`, declaration `FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add`; the repository is private at upload time).

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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

theorem FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add_408915f [IsFiniteMeasure μ]
    (dx : Measure E) (f : E → EReal) (hμ : μ ≠ 0) (hf : PotentialIntegrable f μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      let c := legendre (legendre (lowerTruncate f (n : ℝ)))
      ConvexPotential c ∧ LowerSemicontinuous c ∧ PotentialIntegrable c μ ∧
        variationalFunctional dx μ f ≤ variationalFunctional dx μ c + (ε : EReal) := by sorry
