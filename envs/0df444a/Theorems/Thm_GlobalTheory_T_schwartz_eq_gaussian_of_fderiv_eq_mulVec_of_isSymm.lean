-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm
-- name    : GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:31.49507+00:00
-- url     : https://prove2.me/theorems/f5af9067-9400-4ce6-bc4c-c95ef60e8b00
-- title:
--   T: schwartz eq gaussian of fderiv eq mul Vec of is Symm
-- statement:
--   The T construction uses the schwartz eq gaussian of fderiv eq mul Vec of is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzEqGaussianOfFderivEqMulVecStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzEqGaussianOfFderivEqMulVecStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVec
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzEqGaussianOfFderivEqMulVecStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_eq_gaussian_of_fderiv_eq_mulVec_of_isSymm : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : Sch l), τ.IsSymm → (∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) → ∀ x : EuclideanSpace ℝ l, f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by sorry
