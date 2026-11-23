-- Prove2me | Theorems.Thm_GlobalTheory_SplitEmbSep_norm_le_one_of_isIntegral
-- name    : GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:14.178935+00:00
-- url     : https://prove2.me/theorems/d813563c-d2a2-46f3-8467-9b2d45e4b8cf
-- title:
--   Split Emb Sep: norm le one of is Integral
-- statement:
--   The Split Emb Sep construction uses the norm le one of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsNormSubEqOne.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsNormSubEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.SplitEmbSep
open NumberField

theorem GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral {C : Type*} [NormedField C] [IsUltrametricDist C]
    {x : C} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by sorry
