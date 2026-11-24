-- Prove2me | Theorems.Thm_GlobalTheory_exists_natCast_mem_differentIdeal_pow_le
-- name    : GlobalTheory.exists_natCast_mem_differentIdeal_pow_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:49.007076+00:00
-- url     : https://prove2.me/theorems/422f1014-0446-481d-bcf4-c7d0204eaa1c
-- title:
--   Global Theory: exists nat Cast mem different Ideal pow le
-- statement:
--   The Global Theory construction uses the exists nat Cast mem different Ideal pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLe.lean#L80-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsNatCastMemDifferentIdealPowLe.lean#L80-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNatCastMemDifferentIdealPowLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Pointwise
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem GlobalTheory.exists_natCast_mem_differentIdeal_pow_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E], ∃ N : ℕ, 0 < N ∧
      ((N : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) ∧
      (N : ℝ) ^ Module.finrank ℚ E ≤ |(NumberField.discr E : ℝ)| ^ 2 := by sorry
