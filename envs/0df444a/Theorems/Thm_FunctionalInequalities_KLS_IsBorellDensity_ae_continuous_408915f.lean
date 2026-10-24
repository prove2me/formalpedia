-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_IsBorellDensity_ae_continuous_408915f
-- name    : FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:20:25.91819+00:00
-- url     : https://prove2.me/theorems/a3b26035-3bfd-4cec-8d46-91a43d5c2cd7
-- title:
--   Almost-Everywhere Continuity of Finite-Dimensional Borell Densities
-- statement:
--   This statement establishes almost-everywhere continuity for a finite-dimensional `IsBorellDensity`.
--
--   Let $V$ be a finite-dimensional real normed vector space equipped with its Borel measurable structure, let $m$ be an additive Haar measure on $V$, let $ν$ be a measure on $V$, and let $ρ : V → ℝ$ satisfy `IsBorellDensity ν m ρ`. Then
--
--   $$
--   \text{for }m\text{-almost every }x\in V,\qquad \operatorname{ContinuousAt}(ρ,x).
--   $$
--
--   This is a technical regularity result used when passing from pointwise properties of Borell densities to almost-everywhere statements.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Basic.lean#L167-L187 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.BorellRepresentation.Basic`, declaration `FunctionalInequalities.KLS.IsBorellDensity.ae_continuous`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Borel
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set Topology Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section Representative
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
variable [FiniteDimensional ℝ V]
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.IsBorellDensity
end FunctionalInequalities.KLS.IsBorellDensity
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.IsBorellDensity

theorem FunctionalInequalities.KLS.IsBorellDensity.ae_continuous_408915f {ν m : Measure V} [m.IsAddHaarMeasure]
    {ρ : V → ℝ} (h : IsBorellDensity ν m ρ) :
    ∀ᵐ x ∂m, ContinuousAt ρ x := by sorry
