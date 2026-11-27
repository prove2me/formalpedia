-- Prove2me | Theorems.Thm_GlobalTheory_exists_section_jet_ne_zero
-- name    : GlobalTheory.exists_section_jet_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:48.244827+00:00
-- url     : https://prove2.me/theorems/4d26d41d-0dd2-4a13-9bb5-be3a8423771e
-- title:
--   Global Theory: exists section jet ne zero
-- statement:
--   The Global Theory construction uses the exists section jet ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L277-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L277-L300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open ThetaJet
open Classical

theorem GlobalTheory.exists_section_jet_ne_zero {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (D q : ℕ) (hq : 3 * D + 2 ≤ q) (P : MvPolynomial ι ℂ) (hP : P ≠ 0) (hD : P.totalDegree ≤ D) :
    ∃ F : EuclideanSpace ℂ ι → ℂ, Differentiable ℂ F ∧
      (∀ γ ∈ lat Y.b, ∀ v, F (v + γ) = Y.ka γ ^ q * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F v) ∧
      polyDeriv P (fun i => EuclideanSpace.single i 1) F 0 ≠ 0 := by sorry
