-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_408915f
-- name    : FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:52.427277+00:00
-- url     : https://prove2.me/theorems/864118fa-fc7f-4a20-84cb-c1d7aa1c5bfd
-- title:
--   Energy-Preserving Ambient Extension Of An Intrinsic Test
-- statement:
--   This theorem extends an intrinsic smooth-gradient test to the ambient space without changing its intrinsic restriction or raw energy.
--
--   Let $E$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology, let $\mu$ be a probability measure on $E$, and let $g$ be a smooth-gradient test for the intrinsic measure associated with $\mu$. Then there exists an ambient smooth-gradient test $f$ such that, for every intrinsic coordinate $v$,
--
--   $$
--    f(\operatorname{reconstruct}_{\mu}(v))=g(v),
--   $$
--
--   and
--
--   $$
--   \operatorname{toIntrinsicL2}(\mu)(f.\operatorname{toL2})=g.\operatorname{toL2},
--   \qquad
--   f.\operatorname{energy}=g.\operatorname{energy}.
--   $$
--
--   The declaration is `exists_ambient_extension`. The equality of energies is equality of the raw test-energy values, and the construction applies without a density or second-moment assumption on $\mu$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L154-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, declaration `FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Energy
end FunctionalInequalities.Energy
open FunctionalInequalities FunctionalInequalities.Energy
section
namespace FunctionalInequalities.Energy.SmoothGradient
end FunctionalInequalities.Energy.SmoothGradient
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient
open Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)
section
namespace FunctionalInequalities.Energy.SmoothGradient.Test
end FunctionalInequalities.Energy.SmoothGradient.Test
open FunctionalInequalities FunctionalInequalities.Energy FunctionalInequalities.Energy.SmoothGradient FunctionalInequalities.Energy.SmoothGradient.Test

theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension_408915f
    (g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ)) :
    ∃ f : Energy.SmoothGradient.Test μ,
      (∀ v, f (Probability.reconstruct μ v) = g v) ∧
      toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy := by sorry
