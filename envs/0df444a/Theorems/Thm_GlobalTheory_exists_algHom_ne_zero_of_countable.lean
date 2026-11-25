-- Prove2me | Theorems.Thm_GlobalTheory_exists_algHom_ne_zero_of_countable
-- name    : GlobalTheory.exists_algHom_ne_zero_of_countable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:32.351809+00:00
-- url     : https://prove2.me/theorems/5b76b779-7cf1-5887-8306-aedb0c792876
-- title:
--   Global Theory: exists alg Hom ne zero of countable
-- statement:
--   The Global Theory construction uses the exists alg Hom ne zero of countable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomNeZeroOfCountable.lean#L29-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsAlgHomNeZeroOfCountable.lean#L29-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsAlgHomNeZeroOfCountable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_algHom_ne_zero_of_countable (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ s : E →ₐ[ℂ] ℂ, ∀ r ∈ T, s r ≠ 0 := by sorry
