-- Prove2me | Theorems.Thm_GlobalTheory_schwartz_eq_gaussian_of_fderiv_eq_mulVec
-- name    : GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:31.227243+00:00
-- url     : https://prove2.me/theorems/dd988d4a-4d3d-46ab-975d-c4e9d609e1e6
-- title:
--   Global Theory: schwartz eq gaussian of fderiv eq mul Vec
-- statement:
--   The Global Theory construction uses the schwartz eq gaussian of fderiv eq mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzEqGaussianOfFderivEqMulVec.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzEqGaussianOfFderivEqMulVec.lean#L9-L48

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory

theorem GlobalTheory.schwartz_eq_gaussian_of_fderiv_eq_mulVec :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm →
      (∀ (a : l) (x : EuclideanSpace ℝ l),
        fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) →
      ∀ x : EuclideanSpace ℝ l,
        f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by sorry
