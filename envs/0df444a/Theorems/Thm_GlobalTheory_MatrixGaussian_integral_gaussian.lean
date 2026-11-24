-- Prove2me | Theorems.Thm_GlobalTheory_MatrixGaussian_integral_gaussian
-- name    : GlobalTheory.MatrixGaussian.integral_gaussian
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:17.248956+00:00
-- url     : https://prove2.me/theorems/772caabc-7a45-4b31-ab6d-c0fb10c7210c
-- title:
--   Matrix Gaussian: integral gaussian
-- statement:
--   The Matrix Gaussian construction uses the integral gaussian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L95-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L95-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralComplexGaussianPosDefHermitianPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.MatrixGaussian
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.MatrixGaussian.integral_gaussian (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : (A + Aᴴ).PosDef) :
    A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by sorry
