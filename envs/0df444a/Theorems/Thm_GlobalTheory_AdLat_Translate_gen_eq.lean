-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Translate_gen_eq
-- name    : GlobalTheory.AdLat.Translate.gen_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:50.288674+00:00
-- url     : https://prove2.me/theorems/0d63d302-3b98-47e9-9543-d464a6aa147f
-- title:
--   Translate: gen eq
-- statement:
--   The Translate construction uses the gen eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslate.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslate.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
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
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.Translate.gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (a ⊗ₜ[F] x i : RA F E)) = (a ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by sorry
