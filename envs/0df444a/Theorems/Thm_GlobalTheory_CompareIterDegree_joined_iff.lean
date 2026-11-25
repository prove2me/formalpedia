-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_joined_iff
-- name    : GlobalTheory.CompareIterDegree.joined_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:57:40.663022+00:00
-- url     : https://prove2.me/theorems/cfe6f744-d934-4b02-b658-46574eea252c
-- title:
--   Compare Iter Degree: joined iff
-- statement:
--   The Compare Iter Degree construction uses the joined iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L474-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L474-L500

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

theorem GlobalTheory.CompareIterDegree.joined_iff {n : ℕ} (Q : Set (Fin n → ℝ)) (μ ν : Fin n → ℝ) :
    Relation.EqvGen (fun x y => x ∈ Q ∧ y ∈ Q ∧ ∃ s, y = x + Pi.single s 1) μ ν ↔
      Relation.ReflTransGen (StepIn Q) μ ν := by sorry
