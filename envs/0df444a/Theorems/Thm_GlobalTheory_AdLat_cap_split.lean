-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_cap_split
-- name    : GlobalTheory.AdLat.cap_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:40:53.612813+00:00
-- url     : https://prove2.me/theorems/ad5af481-9302-4eb0-8dfa-4228db3b25f9
-- title:
--   Ad Lat: cap split
-- statement:
--   The Ad Lat construction uses the cap split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionRationalPointsAndApproximation.lean#L49-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionRationalPointsAndApproximation.lean#L49-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
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
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
omit [NumberField E]

theorem GlobalTheory.AdLat.cap_split (r : F) (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (algebraMap F (FiniteAdeleRing (𝓞 F) F) r + d • a) ⊗ₜ[F] x i : Fin n → RA F E)
      = fv F (algebraMap F E r • x) + d • (fun i => a ⊗ₜ[F] x i : Fin n → RA F E) := by sorry
