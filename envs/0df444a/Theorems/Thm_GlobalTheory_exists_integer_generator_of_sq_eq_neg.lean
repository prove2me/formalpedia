-- Prove2me | Theorems.Thm_GlobalTheory_exists_integer_generator_of_sq_eq_neg
-- name    : GlobalTheory.exists_integer_generator_of_sq_eq_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:19.49498+00:00
-- url     : https://prove2.me/theorems/c029a729-c36c-4ce1-88c7-9fc4a390b705
-- title:
--   Global Theory: exists integer generator of sq eq neg
-- statement:
--   The Global Theory construction uses the exists integer generator of sq eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L93-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/RingOfIntegersSqrtNegThreeModFour.lean#L93-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory
open QuadraticZeta

theorem GlobalTheory.exists_integer_generator_of_sq_eq_neg {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (h2 : finrank ℚ K = 2) (hsq : Squarefree d) (hd : d % 4 = 3) {r : K} (hr : r ^ 2 = -d) :
    ∃ w : 𝓞 K, 2 * (w : K) = 1 + r ∧ ∀ c : 𝓞 K, ∃ m n : ℤ, c = m + n * w := by sorry
