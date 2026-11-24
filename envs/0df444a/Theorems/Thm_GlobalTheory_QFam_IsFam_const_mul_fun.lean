-- Prove2me | Theorems.Thm_GlobalTheory_QFam_IsFam_const_mul_fun
-- name    : GlobalTheory.QFam.IsFam.const_mul_fun
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:00:09.034506+00:00
-- url     : https://prove2.me/theorems/b0b5dccc-693d-47d4-8c6a-9991319b9f47
-- title:
--   Is Fam: const mul fun
-- statement:
--   The Is Fam construction uses the const mul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L24-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyAlgebraClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ModularForm
variable {ι : Type} {act : ι → SL(2, ℤ) → ι}

theorem GlobalTheory.QFam.IsFam.const_mul_fun {w : ℤ} {f : ι → ℍ → ℂ} (c : ℂ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ := by sorry
