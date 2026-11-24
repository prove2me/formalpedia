-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_unitary_iff_matrix
-- name    : GlobalTheory.UnRep.Compare.unitary_iff_matrix
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:03.778828+00:00
-- url     : https://prove2.me/theorems/091b5732-2a03-48c3-b0ae-6cbd32fca78b
-- title:
--   Compare: unitary iff matrix
-- statement:
--   The Compare construction uses the unitary iff matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L309-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L309-L328

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

theorem GlobalTheory.UnRep.Compare.unitary_iff_matrix {R : Type} [CommRing R] {n : ℕ} (s : R →+* R) (G g : Matrix (Fin n) (Fin n) R) :
    (∀ x y : Fin n → R, ∑ a, ∑ b, (g *ᵥ x) a * G a b * s ((g *ᵥ y) b) = ∑ a, ∑ b, x a * G a b * s (y b)) ↔
      gᵀ * G * g.map s = G := by sorry
