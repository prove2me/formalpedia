-- Prove2me | Theorems.Thm_Newton_eLpNorm_translate_right
-- name    : Newton.eLpNorm_translate_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:25:09.668745+00:00
-- url     : https://prove2.me/theorems/27c4452e-0acb-4ae9-9ae0-07d486e94bdf
-- title:
--   Newton: e Lp Norm translate right
-- statement:
--   The Newton construction uses the e Lp Norm translate right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L364-L379
-- source:
--   https://github.com/frourios/newton/blob/780b377bed436d905bd76c156cd76bda08b1c786/Newton/Analysis/Convolution/Auxiliary.lean#L364-L379

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}

theorem Newton.eLpNorm_translate_right
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [TopologicalSpace G]
    [MeasurableAdd₂ G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (f : G → ℂ) (p : ℝ≥0∞) (a : G)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f (x - a)) p μ = eLpNorm f p μ := by sorry
