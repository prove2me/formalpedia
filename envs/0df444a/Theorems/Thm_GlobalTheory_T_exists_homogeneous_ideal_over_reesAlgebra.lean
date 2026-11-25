-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_homogeneous_ideal_over_reesAlgebra
-- name    : GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:53:48.843256+00:00
-- url     : https://prove2.me/theorems/7891f92a-6e8b-4c8b-b291-49836d678591
-- title:
--   T: exists homogeneous ideal over rees Algebra
-- statement:
--   The T construction uses the exists homogeneous ideal over rees Algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomogeneousIdealOverReesAlgebraStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHomogeneousIdealOverReesAlgebraStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra : ∀ (R : Type) [CommRing R] (I : Ideal R) (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, coeff m F ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ 𝔞 : Ideal (MvPolynomial (Fin (n + 1)) (reesAlgebra I)), (∀ F ∈ 𝔞, ∀ d, homogeneousComponent d F ∈ 𝔞) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) (reesAlgebra I)), F.IsHomogeneous t → (F ∈ 𝔞 ↔ ∀ (e : ℕ) (G : MvPolynomial (Fin (n + 1)) R), (∀ m, coeff m G = (coeff m F).1.coeff e) → G ∈ J e) := by sorry
