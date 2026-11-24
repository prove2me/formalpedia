-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_congOneAt_of_congAtA
-- name    : GlobalTheory.UnRep.Compare.congOneAt_of_congAtA
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:57.580134+00:00
-- url     : https://prove2.me/theorems/5ccaa9a6-12b0-4eca-b736-f18fbc8b614c
-- title:
--   Compare: cong One At of cong At A
-- statement:
--   The Compare construction uses the cong One At of cong At A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L194-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L194-L210

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

theorem GlobalTheory.UnRep.Compare.congOneAt_of_congAtA {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) (h : CongAtA F L N D k) :
    CongOneAt N D (L : Set (Fin n → E)) k := by sorry
