-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_Compare_exists_inv
-- name    : GlobalTheory.UnRep.Compare.exists_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:27.152269+00:00
-- url     : https://prove2.me/theorems/c1b2458a-2dc5-4400-831d-2d4e52f300b4
-- title:
--   Compare: exists inv
-- statement:
--   The Compare construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L66-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsSplitPlaceOfSplitPl.lean#L66-L84

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

theorem GlobalTheory.UnRep.Compare.exists_inv (m : ℕ) (hm : m ≠ 0) (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∈ S, (m : 𝓞 F) ∉ v.asIdeal) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      (m : RA F E) * (a ⊗ₜ[F] (1 : E)) = ind S ⊗ₜ[F] (1 : E) := by sorry
