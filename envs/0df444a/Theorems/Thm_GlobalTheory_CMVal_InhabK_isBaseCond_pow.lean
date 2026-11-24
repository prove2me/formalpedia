-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_isBaseCond_pow
-- name    : GlobalTheory.CMVal.InhabK.isBaseCond_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:40.468969+00:00
-- url     : https://prove2.me/theorems/e28c2621-4797-4f4f-b39e-4fd52b543d07
-- title:
--   Inhab K: is Base Cond pow
-- statement:
--   The Inhab K construction uses the is Base Cond pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L166-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L166-L182

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK

theorem GlobalTheory.CMVal.InhabK.isBaseCond_pow (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) (n : ℕ) :
    IsBaseCond (v.asIdeal ^ n) ↔ n = 1 ∨ n = 2 := by sorry
