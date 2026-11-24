-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_unramFin_K
-- name    : GlobalTheory.CMVal.InhabK.unramFin_K
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:26.976827+00:00
-- url     : https://prove2.me/theorems/53b82023-329d-40cf-9b22-76308e40206e
-- title:
--   Inhab K: unram Fin K
-- statement:
--   The Inhab K construction uses the unram Fin K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L116-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L116-L127

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
attribute [local instance] FractionRing.liftAlgebra

theorem GlobalTheory.CMVal.InhabK.unramFin_K : UnramFin K := by sorry
