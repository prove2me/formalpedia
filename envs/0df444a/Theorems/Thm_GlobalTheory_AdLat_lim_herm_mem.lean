-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_lim_herm_mem
-- name    : GlobalTheory.AdLat.lim_herm_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:21:04.066744+00:00
-- url     : https://prove2.me/theorems/78de9dcb-7e5c-4434-a8ca-618ba03be399
-- title:
--   Ad Lat: lim herm mem
-- statement:
--   The Ad Lat construction uses the lim herm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealDivisibleEqZero.lean#L89-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealDivisibleEqZero.lean#L89-L104

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

theorem GlobalTheory.AdLat.lim_herm_mem (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {Λ : Set (Fin n → E)} {J : Set E}
    (h : ∀ x ∈ Λ, ∀ y ∈ Λ, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J) {x y : Fin n → RA F E}
    (hx : x ∈ hat F Λ) (hy : y ∈ hat F Λ) : hermBil F c G x y ∈ hat1 F J := by sorry
