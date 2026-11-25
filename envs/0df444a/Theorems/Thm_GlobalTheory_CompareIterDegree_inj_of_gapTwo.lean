-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_inj_of_gapTwo
-- name    : GlobalTheory.CompareIterDegree.inj_of_gapTwo
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:00:44.892797+00:00
-- url     : https://prove2.me/theorems/6168dcb6-0dfd-5235-b969-1add352154ad
-- title:
--   Compare Iter Degree: inj of gap Two
-- statement:
--   The Compare Iter Degree construction uses the inj of gap Two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L286-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L286-L290

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

theorem GlobalTheory.CompareIterDegree.inj_of_gapTwo {n : ℕ} {μ : Fin n → ℝ} (h : GapTwo μ) : Function.Injective μ := by sorry
