-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_congAtA_of_congOneAt
-- name    : GlobalTheory.UnRep.Compare.congAtA_of_congOneAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:18:21.059894+00:00
-- url     : https://prove2.me/theorems/0df2baa3-d627-4865-b1c0-54068d81b72a
-- title:
--   Compare: cong At A of cong One At
-- statement:
--   The Compare construction uses the cong At A of cong One At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L247-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L247-L284

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

theorem GlobalTheory.UnRep.Compare.congAtA_of_congOneAt {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) {N D d : ℕ} (hN : N ≠ 0) (hD : D ≠ 0)
    (hd : d ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (hk : ∀ z ∈ hat F (L : Set (Fin n → E)), d • k *ᵥ z ∈ hat F (L : Set (Fin n → E)))
    (h : CongOneAt N D (L : Set (Fin n → E)) k) {t j : ℕ} (hdvd : D * d ∣ t * N ^ j) :
    ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (k *ᵥ z - z) = D • w := by sorry
