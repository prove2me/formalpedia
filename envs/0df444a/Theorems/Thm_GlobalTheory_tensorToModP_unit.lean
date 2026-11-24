-- Prove2me | Theorems.Thm_GlobalTheory_tensorToModP_unit
-- name    : GlobalTheory.tensorToModP_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:23:46.347888+00:00
-- url     : https://prove2.me/theorems/35a2bb89-0777-4c96-bc57-00b0f8d8c7f8
-- title:
--   Global Theory: tensor To Mod P unit
-- statement:
--   The Global Theory construction uses the tensor To Mod P unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L47-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory

theorem GlobalTheory.tensorToModP_unit (p : ℕ) (M : ModuleCat.{0} ℤ) (m : M) :
    tensorToModP p M
      (((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom m) =
      Submodule.Quotient.mk m := by sorry
