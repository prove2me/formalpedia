-- Prove2me | Theorems.Thm_GlobalTheory_exists_short_independent_integers
-- name    : GlobalTheory.exists_short_independent_integers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:36.168441+00:00
-- url     : https://prove2.me/theorems/642991ef-a334-4016-a84d-d975c8a4a7d2
-- title:
--   Global Theory: exists short independent integers
-- statement:
--   The Global Theory construction uses the exists short independent integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsShortIndependentIntegers.lean#L78-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsShortIndependentIntegers.lean#L78-L191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsShortIndependentIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Submodule
open scoped nonZeroDivisors
open GlobalTheory
open NumberField Module Submodule
open scoped nonZeroDivisors

theorem GlobalTheory.exists_short_independent_integers (K : Type) [Field K] [NumberField K] :
    ∃ ω : Fin (Module.finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun k => (ω k : K)) ∧
      ∀ (s : K →+* ℂ) k, ‖s (ω k : K)‖ ≤ (Module.finrank ℚ K : ℝ) ^ 3 *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) := by sorry
