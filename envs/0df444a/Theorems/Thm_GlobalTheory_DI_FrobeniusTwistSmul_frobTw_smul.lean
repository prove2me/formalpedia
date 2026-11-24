-- Prove2me | Theorems.Thm_GlobalTheory_DI_FrobeniusTwistSmul_frobTw_smul
-- name    : GlobalTheory.DI.FrobeniusTwistSmul.frobTw_smul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:34:51.556891+00:00
-- url     : https://prove2.me/theorems/ff5ea948-e45b-4245-bfa3-7f36937a7246
-- title:
--   Frobenius Twist Smul: frob Tw smul
-- statement:
--   The Frobenius Twist Smul construction uses the frob Tw smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExteriorAlgebraExtensionOfFrobeniusSemilin.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExteriorAlgebraExtensionOfFrobeniusSemilin.lean#L15-L18

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExteriorAlgebraExtensionOfFrobeniusSemilin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FrobeniusTwistSmul
variable (K : Type) [CommRing K] (p : ℕ) [Fact p.Prime] [CharP K p] (W : Type) [AddCommGroup W] [Module K W]

theorem GlobalTheory.DI.FrobeniusTwistSmul.frobTw_smul (c : K) (x : FrobTw K p W) :
    c • x = ((c ^ p • (show W from x) : W) : FrobTw K p W) := by sorry
