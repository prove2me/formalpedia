-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_isCMType_places
-- name    : GlobalTheory.CMVal.InhabK.isCMType_places
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:07.839809+00:00
-- url     : https://prove2.me/theorems/ae8a9398-c1d6-4a66-a576-a2fcecc3f2cf
-- title:
--   Inhab K: is CMType places
-- statement:
--   The Inhab K construction uses the is CMType places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L15-L23

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
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.InhabK.isCMType_places : IsCMType (fun w : InfinitePlace E => w.embedding) := by sorry
