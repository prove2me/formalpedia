-- Prove2me | Theorems.Thm_GlobalTheory_HCA_contDiff_mul_of_contDiffOn_of_tsupport
-- name    : GlobalTheory.HCA.contDiff_mul_of_contDiffOn_of_tsupport
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:01:06.11917+00:00
-- url     : https://prove2.me/theorems/d4ad4774-6dc2-4c36-abd0-24efbe89dd3d
-- title:
--   HCA: cont Diff mul of cont Diff On of tsupport
-- statement:
--   The HCA construction uses the cont Diff mul of cont Diff On of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L37-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeakSolutionOfSmoothSolution.lean#L37-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralMulIterPartialDerivEqNegPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.contDiff_mul_of_contDiffOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {b φ : E d → ℂ} (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by sorry
