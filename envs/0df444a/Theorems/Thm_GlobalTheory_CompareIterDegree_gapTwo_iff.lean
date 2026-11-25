-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_gapTwo_iff
-- name    : GlobalTheory.CompareIterDegree.gapTwo_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:45.570931+00:00
-- url     : https://prove2.me/theorems/b0d872b6-25d6-5be3-8b47-0dc411fd848d
-- title:
--   Compare Iter Degree: gap Two iff
-- statement:
--   The Compare Iter Degree construction uses the gap Two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L300-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L300-L309

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

theorem GlobalTheory.CompareIterDegree.gapTwo_iff {n : ℕ} {μ : Fin n → ℝ} (h : StrictAnti μ) :
    (∀ a b, a < b → 2 ≤ μ a - μ b) ↔ GapTwo μ := by sorry
