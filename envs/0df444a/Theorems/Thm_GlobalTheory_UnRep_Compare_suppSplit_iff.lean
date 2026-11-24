-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_suppSplit_iff
-- name    : GlobalTheory.UnRep.Compare.suppSplit_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:17:52.105962+00:00
-- url     : https://prove2.me/theorems/8c8548f9-7825-45dd-b9a0-e625afb46bb0
-- title:
--   Compare: supp Split iff
-- statement:
--   The Compare construction uses the supp Split iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L183-L186

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

theorem GlobalTheory.UnRep.Compare.suppSplit_iff (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ} (N : ℕ)
    (h : Matrix (Fin n) (Fin n) (RA F E)) : SuppSplit c N h ↔ SupportedAtSplit N h := by sorry
