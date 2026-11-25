-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_round_gap
-- name    : GlobalTheory.CompareIterDegree.round_gap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:58:10.116018+00:00
-- url     : https://prove2.me/theorems/ffbb4295-f9d3-4939-ad81-47ffdc252891
-- title:
--   Compare Iter Degree: round gap
-- statement:
--   The Compare Iter Degree construction uses the round gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L347-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L347-L366

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

theorem GlobalTheory.CompareIterDegree.round_gap {n : ℕ} {μ : Fin n → ℝ} (hg : GapTwo μ) (s : Fin n) (g : ℝ → ℤ) (hm : Monotone g)
    (h2 : ∀ x, g (x + 2) = g x + 2) (h0 : g 0 = 0) :
    GapTwo (fun c => -(g (μ s - μ c) : ℝ)) ∧ ∀ c, c ≠ s → 0 < (μ s - μ c) * g (μ s - μ c) := by sorry
