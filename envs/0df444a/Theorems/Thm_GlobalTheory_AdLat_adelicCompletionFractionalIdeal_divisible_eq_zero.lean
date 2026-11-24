-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_adelicCompletionFractionalIdeal_divisible_eq_zero
-- name    : GlobalTheory.AdLat.adelicCompletionFractionalIdeal_divisible_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:51.003055+00:00
-- url     : https://prove2.me/theorems/acbbac32-981e-4659-8795-c8d14dfcf09d
-- title:
--   Ad Lat: adelic Completion Fractional Ideal divisible eq zero
-- statement:
--   The Ad Lat construction uses the adelic Completion Fractional Ideal divisible eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealDivisibleEqZero.lean#L108-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealDivisibleEqZero.lean#L108-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]

theorem GlobalTheory.AdLat.adelicCompletionFractionalIdeal_divisible_eq_zero (J : FractionalIdeal (𝓞 E)⁰ E) (z : RA F E)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ hat1 F (J : Set E), z = N • w) : z = 0 := by sorry
