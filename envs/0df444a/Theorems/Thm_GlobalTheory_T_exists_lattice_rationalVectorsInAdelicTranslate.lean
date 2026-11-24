-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_lattice_rationalVectorsInAdelicTranslate
-- name    : GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:21:53.221108+00:00
-- url     : https://prove2.me/theorems/1b49d4c9-9225-4cbb-a721-196272899552
-- title:
--   T: exists lattice rational Vectors In Adelic Translate
-- statement:
--   The T construction uses the exists lattice rational Vectors In Adelic Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslateStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslateStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_lattice_rationalVectorsInAdelicTranslate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by sorry
