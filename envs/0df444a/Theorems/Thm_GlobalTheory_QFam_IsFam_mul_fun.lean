-- Prove2me | Theorems.Thm_GlobalTheory_QFam_IsFam_mul_fun
-- name    : GlobalTheory.QFam.IsFam.mul_fun
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:59:05.972731+00:00
-- url     : https://prove2.me/theorems/56a19222-1805-49a4-9e5a-2fc41f81583a
-- title:
--   Is Fam: mul fun
-- statement:
--   The Is Fam construction uses the mul fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyAlgebraClosure.lean#L37-L45

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

theorem GlobalTheory.QFam.IsFam.mul_fun {w w' : ℤ} {f g : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (hg : _root_.GlobalTheory.QFam.IsFam act w' g) :
    _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ := by sorry
