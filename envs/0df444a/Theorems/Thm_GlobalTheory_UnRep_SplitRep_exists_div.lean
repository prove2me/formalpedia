-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SplitRep_exists_div
-- name    : GlobalTheory.UnRep.SplitRep.exists_div
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:43.162217+00:00
-- url     : https://prove2.me/theorems/a2874d5d-58da-4dc7-85d4-944254088999
-- title:
--   Split Rep: exists div
-- statement:
--   The Split Rep construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L121-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitaryAdelicDecompositionSplitSupport.lean#L121-L135

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryAdelicDecompositionSplitSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
variable [NumberField E]
omit [NumberField E]

theorem GlobalTheory.UnRep.SplitRep.exists_div (m : 𝓞 F) (hm : m ≠ 0) (e : FiniteAdeleRing (𝓞 F) F)
    (h1 : ∀ v : HeightOneSpectrum (𝓞 F), m ∈ v.asIdeal → e v = 1)
    (h0 : ∀ v : HeightOneSpectrum (𝓞 F), m ∉ v.asIdeal → e v = 0) :
    ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ (m : F) • a = 1 - e := by sorry
