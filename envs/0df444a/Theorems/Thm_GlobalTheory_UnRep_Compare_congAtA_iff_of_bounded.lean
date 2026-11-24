-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_iff_of_bounded
-- name    : GlobalTheory.UnRep.Compare.congAtA_iff_of_bounded
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:19.270627+00:00
-- url     : https://prove2.me/theorems/f3dea477-5f5c-4d81-b534-a66e3ad97400
-- title:
--   Compare: cong At A iff of bounded
-- statement:
--   The Compare construction uses the cong At A iff of bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L286-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L286-L292

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

theorem GlobalTheory.UnRep.Compare.congAtA_iff_of_bounded {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E))) :
    CongAtA F L N D k ↔ CongOneAt N D (L : Set (Fin n → E)) k := by sorry
