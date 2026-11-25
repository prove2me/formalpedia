-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_chain_bound
-- name    : GlobalTheory.CompareIterDegree.chain_bound
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:32.413663+00:00
-- url     : https://prove2.me/theorems/1f98bdc1-5246-5591-ae29-653fbe7724a5
-- title:
--   Compare Iter Degree: chain bound
-- statement:
--   The Compare Iter Degree construction uses the chain bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L259-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L259-L274

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DegreeProportionalWords
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GapSubsetOfSetBoundIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CompareIterDegree
open Formalism.QuantumDeterminants Formalism.HermitianLatticeCounting.ExpansionTerms GlobalTheory.IndefiniteRowSideFullHecke.DegreeProportionalWords

theorem GlobalTheory.CompareIterDegree.chain_bound {α : Type} [DecidableEq α] (F : Finset α → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo) (I : Finset α)
    (hpos : ∀ J ⊆ I, 0 < F J)
    (hstep : ∀ J s, s ∉ J → insert s J ⊆ I → lo ≤ F (insert s J) / F J ∧ F (insert s J) / F J ≤ hi) :
    lo ^ I.card ≤ F I / F ∅ ∧ F I / F ∅ ≤ hi ^ I.card := by sorry
