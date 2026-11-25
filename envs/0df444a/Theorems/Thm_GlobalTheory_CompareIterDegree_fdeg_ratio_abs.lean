-- Prove2me | Theorems.Thm_GlobalTheory_CompareIterDegree_fdeg_ratio_abs
-- name    : GlobalTheory.CompareIterDegree.fdeg_ratio_abs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:59:30.178216+00:00
-- url     : https://prove2.me/theorems/f3d2a668-42cc-5223-880b-926f71849f4f
-- title:
--   Compare Iter Degree: fdeg ratio abs
-- statement:
--   The Compare Iter Degree construction uses the fdeg ratio abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L158-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GapSubsetOfSetBoundIntegral.lean#L158-L212

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

theorem GlobalTheory.CompareIterDegree.fdeg_ratio_abs {n : ℕ} (μ : Fin n → ℝ) (s : Fin n) (t : ℝ) (hinj : Function.Injective μ) :
    fdegHC (μ + Pi.single s t) / fdegHC μ = ∏ c ∈ univ.erase s, |(μ s + t - μ c) / (μ s - μ c)| := by sorry
