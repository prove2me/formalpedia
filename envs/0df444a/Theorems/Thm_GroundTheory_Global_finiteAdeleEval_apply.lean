-- Prove2me | Theorems.Thm_GroundTheory_Global_finiteAdeleEval_apply
-- name    : GroundTheory.Global.finiteAdeleEval_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:16.943358+00:00
-- url     : https://prove2.me/theorems/0d5be158-f486-463c-a817-59ea7239cd92
-- title:
--   Global: finite Adele Eval apply
-- statement:
--   The Global construction uses the finite Adele Eval apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L73-L75

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.finiteAdeleEval_apply (x : HeightOneSpectrum (𝓞 K)) (a : 𝔸ᶠ[K]) :
    finiteAdeleEval x a = a x := by sorry

attribute [defeq] GroundTheory.Global.finiteAdeleEval_apply
