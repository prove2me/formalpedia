-- Prove2me | Theorems.Thm_GlobalTheory_DetInv_iotaScalar_one
-- name    : GlobalTheory.DetInv.iotaScalar_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:04:13.221089+00:00
-- url     : https://prove2.me/theorems/e13fb076-9b73-4320-99eb-d01c5726ae90
-- title:
--   Det Inv: iota Scalar one
-- statement:
--   The Det Inv construction uses the iota Scalar one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IotaScalarOne.lean#L76-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IotaScalarOne.lean#L76-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SandwichMaps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix GlobalTheory.Sandwich TensorProduct
open GlobalTheory GlobalTheory.DetInv
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ]
variable {p O Λ}

theorem GlobalTheory.DetInv.iotaScalar_one {C : Type} [Field C] (N : ℕ) :
    IotaScalar (1 : Matrix (Fin N) (Fin N) C) 0 0 1 := by sorry
