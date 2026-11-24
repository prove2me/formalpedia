-- Prove2me | Theorems.Thm_GlobalTheory_unit_surjective_zmod
-- name    : GlobalTheory.unit_surjective_zmod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:38.638905+00:00
-- url     : https://prove2.me/theorems/5d92c776-8511-4d88-9f8a-10d2454a7f5e
-- title:
--   Global Theory: unit surjective zmod
-- statement:
--   The Global Theory construction uses the unit surjective zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L84-L88

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

theorem GlobalTheory.unit_surjective_zmod (p : ℕ) (M : ModuleCat.{0} ℤ) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj (Int.castRingHom (ZMod p))).unit.app M).hom := by sorry
