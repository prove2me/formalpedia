-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_setOf_not_isIntegralUnitAt
-- name    : GroundTheory.Global.finite_setOf_not_isIntegralUnitAt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:24.161811+00:00
-- url     : https://prove2.me/theorems/be275ef2-66d4-4434-93ad-61005bb842de
-- title:
--   Global: finite set Of not is Integral Unit At
-- statement:
--   The Global construction uses the finite set Of not is Integral Unit At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/FiniteAdeleScaling.lean#L98-L100

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

theorem GroundTheory.Global.finite_setOf_not_isIntegralUnitAt (u : (𝔸ᶠ[K])ˣ) :
    {v | ¬ IsIntegralUnitAt u v}.Finite := by sorry
