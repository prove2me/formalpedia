-- Prove2me | Theorems.Thm_GlobalTheory_HCA_exists_apOp_add_lower_sum
-- name    : GlobalTheory.HCA.exists_apOp_add_lower_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:59.928776+00:00
-- url     : https://prove2.me/theorems/1807d353-68d7-47f9-8479-c3f7931254b0
-- title:
--   HCA: exists ap Op add lower sum
-- statement:
--   The HCA construction uses the exists ap Op add lower sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEllipticWeakSolOfPolynomialLaplacianZero.lean#L17-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEllipticWeakSolOfPolynomialLaplacianZero.lean#L17-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSumSquaresRightDerivPowDifferentialOperatoStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsApOpAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeakSolutionOfSmoothSolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEllipticWeakSolOfPolynomialLaplacianZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA

theorem GlobalTheory.HCA.exists_apOp_add_lower_sum {d : ℕ} (U : Set (E d)) (k : ℕ)
    (A : ℕ → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hA : ∀ i n w, ContDiffOn ℝ ∞ (A i n w) U) (t : ℕ → ℂ) :
    ∀ N ≤ k, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) U) ∧
      (∀ x ξ : E d, symb (2 * k) a x ξ = symb (2 * k) (A k) x ξ) ∧
      ∀ (u : E d → ℂ) (x : E d), apOp (2 * k) a u x =
        apOp (2 * k) (A k) u x + ∑ i ∈ Finset.range N, t i * apOp (2 * i) (A i) u x := by sorry
