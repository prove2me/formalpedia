-- Prove2me | Theorems.Thm_GlobalTheory_T_isSLTwoPermutedModularFamily_iff_values
-- name    : GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:40.420891+00:00
-- url     : https://prove2.me/theorems/4ec3e0ca-5103-4e80-ad8c-a64c83961ffa
-- title:
--   T: is SLTwo Permuted Modular Family iff values
-- statement:
--   The T construction uses the is SLTwo Permuted Modular Family iff values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyIffValuesStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSLTwoPermutedModularFamilyIffValuesStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyIffValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSLTwoPermutedModularFamilyIffValuesStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isSLTwoPermutedModularFamily_iff_values : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ), IsFam act w f ↔ ∀ (i : ι) (γ : SL(2, ℤ)) (τ : ℍ), f i (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) ^ w * f (act i γ) τ := by sorry
