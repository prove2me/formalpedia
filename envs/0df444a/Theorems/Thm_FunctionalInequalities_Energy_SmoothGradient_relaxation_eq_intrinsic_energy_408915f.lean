-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_eq_intrinsic_energy_408915f
-- name    : FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:28:55.157305+00:00
-- url     : https://prove2.me/theorems/da7817f7-4aba-45a5-b364-087bd9c74f99
-- title:
--   Ambient–Intrinsic Relaxation Energy Equality
-- statement:
--   This theorem identifies the ambient and intrinsic smooth-gradient relaxation energies for a finite-dimensional probability measure.
--
--   Let $E$ be a finite-dimensional real inner-product space that is a normed additive commutative group, complete, equipped with a measurable structure and its Borel structure, and having a second-countable topology. Let $\mu$ be a probability measure on $E$.
--
--   The two extended-valued energies, namely `SmoothGradient.relaxation μ` and `SmoothGradient.Intrinsic.energy μ`, are equal as functionals on the common original $L^2(\mu)$ space:
--
--   $$
--   \operatorname{relaxation}(\mu)=\operatorname{Intrinsic.energy}(\mu).
--   $$
--
--   The equality includes the possibility that either energy takes the value $+\infty$. It provides the ambient–intrinsic identification needed to transfer statements between the two relaxed energy constructions, without imposing a density or second-moment assumption on $\mu$.
--
--   **Formalization Note** The energies take values in $[0,\infty]$ and are compared as extended-valued functionals. The statement is restricted to finite-dimensional real inner-product spaces and makes no assumption that the affine support has positive dimension.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L181-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, declaration `FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy`; the repository is private at upload time).

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

theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy_408915f :
    relaxation μ = Intrinsic.energy μ := by sorry
