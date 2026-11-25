-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_step_ratio_eq
-- name    : GlobalTheory.CompareIterDegree.step_ratio_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:58:11.375832+00:00
-- url     : https://prove2.me/theorems/118ce455-a283-4f4d-828b-f0fd9c46f254
-- title:
--   Compare Iter Degree: step ratio eq
-- statement:
--   The Compare Iter Degree construction uses the step ratio eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L246-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L246-L251

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

theorem GlobalTheory.CompareIterDegree.step_ratio_eq {n : ℕ} {μ : Fin n → ℝ} (h : RegInt μ) (s : Fin n) :
    fdegHC (μ + Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s + 1 - μ c) / (μ s - μ c) ∧
    fdegHC (μ - Pi.single s 1) / fdegHC μ = ∏ c ∈ univ.erase s, (μ s - 1 - μ c) / (μ s - μ c) := by sorry
