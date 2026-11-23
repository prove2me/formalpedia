-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_absNorm_of_mem
-- name    : GlobalTheory.CMVal.InhabK.absNorm_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:56.289725+00:00
-- url     : https://prove2.me/theorems/94537448-5edd-46f3-9149-22071e544739
-- title:
--   Inhab K: abs Norm of mem
-- statement:
--   The Inhab K construction uses the abs Norm of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L129-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L129-L142

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

theorem GlobalTheory.CMVal.InhabK.absNorm_of_mem (P : HeightOneSpectrum (𝓞 K)) (h : ((43 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 43 := by sorry
