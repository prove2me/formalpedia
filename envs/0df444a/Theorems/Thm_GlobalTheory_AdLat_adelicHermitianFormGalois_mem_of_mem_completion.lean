-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_adelicHermitianFormGalois_mem_of_mem_completion
-- name    : GlobalTheory.AdLat.adelicHermitianFormGalois_mem_of_mem_completion
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:51.245064+00:00
-- url     : https://prove2.me/theorems/04abc9b8-7eec-4b65-bdff-f36d8288baaa
-- title:
--   Ad Lat: adelic Hermitian Form Galois mem of mem completion
-- statement:
--   The Ad Lat construction uses the adelic Hermitian Form Galois mem of mem completion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicHermitianFormGaloisMemOfMemCompletion.lean#L31-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicHermitianFormGaloisMemOfMemCompletion.lean#L31-L50

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

theorem GlobalTheory.AdLat.adelicHermitianFormGalois_mem_of_mem_completion {S : Set (Fin n → E)} {J : Set E} {z : Fin n → RA F E}
    (hz : ∀ y ∈ S, hermA c G z (fv F y) ∈ hat1 F J) {w : Fin n → RA F E} (hw : w ∈ hat F S) :
    hermA c G z w ∈ hat1 F J := by sorry
