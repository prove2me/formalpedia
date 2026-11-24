-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_isHermForm_iff
-- name    : GlobalTheory.UnRep.Compare.isHermForm_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:25.033666+00:00
-- url     : https://prove2.me/theorems/bc15176b-768f-4d93-8597-9d5a786ff4ce
-- title:
--   Compare: is Herm Form iff
-- statement:
--   The Compare construction uses the is Herm Form iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L366-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L366-L369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.UnRep.Compare.isHermForm_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) :
    IsHermForm c G ↔ c ≠ 1 ∧ (∀ a b, G b a = c (G a b)) ∧ G.det ≠ 0 := by sorry
