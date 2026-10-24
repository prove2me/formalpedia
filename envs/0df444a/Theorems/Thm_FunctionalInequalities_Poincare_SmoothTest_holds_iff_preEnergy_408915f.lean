-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_preEnergy_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:29:35.788289+00:00
-- url     : https://prove2.me/theorems/5a8abc0a-305c-483f-be22-45794c96ef36
-- title:
--   Smooth-Test Bounds Equivalent to Smooth Pre-Energy Test-Family Bounds
-- statement:
--   This statement identifies two fixed-constant formulations of the smooth-gradient Poincaré inequality.
--
--   Let $E$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Let $\mu$ be any probability measure on $E$ and $C\in[0,\infty)$. Let $\mathcal T_\mu$ be the test family `Poincare.TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)`.
--
--   Then
--   $$
--   \operatorname{SmoothTest.Holds}(\mu,C)
--   \quad\Longleftrightarrow\quad
--   \operatorname{TestFamily.Holds}(\mathcal T_\mu,C).
--   $$
--   The left side is `Poincare.SmoothTest.Holds`: variance is at most $C\int\|\nabla f\|^2\,d\mu$ for every $C^\infty$ function $f\in L^2(\mu)$ with integrable squared gradient. The right side is the corresponding inequality on the concrete pre-energy test family.
--
--   This equivalence connects the concrete smooth-test formulation to the test-family interface, without asserting an identification with a relaxed or literature constant.
--
--   **Formalization Note** $C$ is `NNReal` and is coerced to $\mathbb R$ on the left. No moment, log-concavity, density, or positive-dimension assumption is imposed on $\mu$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Comparison.lean#L36-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Comparison`, declaration `FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Core
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
import Definitions.Def_KLS408915f_FunctionalInequalities_L2_MeanVariance
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_L2_Energy
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_Relaxation
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Ambient
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothGradient_Intrinsic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Optimal
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Filter.ENNReal
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

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
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_preEnergy_408915f (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      (TestFamily.ofPreEnergy μ (Energy.SmoothGradient.preEnergy μ)).Holds C := by sorry
