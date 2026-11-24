-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_hermA_fv_fv
-- name    : GlobalTheory.AdLat.hermA_fv_fv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:09.09644+00:00
-- url     : https://prove2.me/theorems/b4361822-da95-439c-9364-83287040513f
-- title:
--   Ad Lat: herm A fv fv
-- statement:
--   The Ad Lat construction uses the herm A fv fv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicHermitianFormGaloisMemOfMemCompletion.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicHermitianFormGaloisMemOfMemCompletion.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionSelfDualOfSelfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicHermitianFormGaloisMemOfMemCompletion
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
  (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.AdLat.hermA_fv_fv (x y : Fin n → E) :
    hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) := by sorry
