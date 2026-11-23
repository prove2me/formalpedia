-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_zeta_prim
-- name    : GlobalTheory.CMVal.InhabK.zeta_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:51.658125+00:00
-- url     : https://prove2.me/theorems/992874e3-75fd-41f6-81d1-54baa3d1635d
-- title:
--   Inhab K: zeta prim
-- statement:
--   The Inhab K construction uses the zeta prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L111-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L111-L112

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

theorem GlobalTheory.CMVal.InhabK.zeta_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta_spec 21 ℚ K).toInteger 21 := by sorry
