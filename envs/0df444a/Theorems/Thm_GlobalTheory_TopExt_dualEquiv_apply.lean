-- Prove2me | Theorems.Thm_GlobalTheory_TopExt_dualEquiv_apply
-- name    : GlobalTheory.TopExt.dualEquiv_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:46.899175+00:00
-- url     : https://prove2.me/theorems/9273c0bb-f235-4323-8caf-25831ef830c8
-- title:
--   Top Ext: dual Equiv apply
-- statement:
--   The Top Ext construction uses the dual Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean#L152-L153

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

theorem GlobalTheory.TopExt.dualEquiv_apply [Module.Finite R F] [Module.Projective R F] (n : ℕ)
    (ξ : ⋀[R]^n (Dual R F)) : dualEquiv R F n ξ = exteriorPower.pairingDual R F n ξ := by sorry

attribute [defeq] GlobalTheory.TopExt.dualEquiv_apply
