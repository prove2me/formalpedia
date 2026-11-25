-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_inj_add_of_gapTwo
-- name    : GlobalTheory.CompareIterDegree.inj_add_of_gapTwo
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:58:31.815625+00:00
-- url     : https://prove2.me/theorems/962ad347-234c-463a-94f1-cd47fd44a142
-- title:
--   Compare Iter Degree: inj add of gap Two
-- statement:
--   The Compare Iter Degree construction uses the inj add of gap Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L292-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L292-L298

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

theorem GlobalTheory.CompareIterDegree.inj_add_of_gapTwo {n : ℕ} {μ e : Fin n → ℝ} (h : GapTwo μ) (he : ∀ a b, |e a - e b| ≤ 1) :
    Function.Injective (μ + e) := by sorry
