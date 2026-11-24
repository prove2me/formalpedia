-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_Dual_val_inv
-- name    : GlobalTheory.UnitLemma.Unr.Dual.val_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:20.535473+00:00
-- url     : https://prove2.me/theorems/3dce42a6-cddc-47dc-bdb0-024af7727238
-- title:
--   Dual: val inv
-- statement:
--   The Dual construction uses the val inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIff.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianDualInvAlgBaseChangeUnramifiedIff.lean#L20-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemRangeOfValNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitTraceUnramifiedExtensionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianDualInvAlgBaseChangeUnramifiedIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem GlobalTheory.UnitLemma.Unr.Dual.val_inv (K : UQ) (x : K.E) : val K.O x⁻¹ = - val K.O x := by sorry
