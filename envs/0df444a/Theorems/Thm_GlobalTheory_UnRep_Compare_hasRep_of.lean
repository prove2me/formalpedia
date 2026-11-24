-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_hasRep_of
-- name    : GlobalTheory.UnRep.Compare.hasRep_of
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:23:13.027514+00:00
-- url     : https://prove2.me/theorems/fd0a36c0-0200-49aa-b744-8b4c101b9640
-- title:
--   Compare: has Rep of
-- statement:
--   The Compare construction uses the has Rep of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L378-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L378-L393

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

theorem GlobalTheory.UnRep.Compare.hasRep_of (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) {n : ℕ}
    {G : Matrix (Fin n) (Fin n) E} (hG : G.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) {N : ℕ} (hN : N ≠ 0)
    (H : HasSplitRepresentatives c G (L : Set (Fin n → E)) N N) : HasRep c G L N := by sorry
