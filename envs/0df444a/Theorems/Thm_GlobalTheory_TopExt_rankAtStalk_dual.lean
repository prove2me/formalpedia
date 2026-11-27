-- Prove2me | Theorems.Thm_GlobalTheory_TopExt_rankAtStalk_dual
-- name    : GlobalTheory.TopExt.rankAtStalk_dual
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:31.725806+00:00
-- url     : https://prove2.me/theorems/8df1a144-32ad-522f-b222-a8c2d5643ce7
-- title:
--   Top Ext: rank At Stalk dual
-- statement:
--   The Top Ext construction uses the rank At Stalk dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L157-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L157-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
variable (F)

theorem GlobalTheory.TopExt.rankAtStalk_dual [Module.Finite R F] [Module.Projective R F] (p : PrimeSpectrum R) :
    rankAtStalk (Dual R F) p = rankAtStalk F p := by sorry
