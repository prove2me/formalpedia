-- Prove2me | Theorems.Thm_GlobalTheory_MatrixGaussian_gaussian_diagonal
-- name    : GlobalTheory.MatrixGaussian.gaussian_diagonal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:18.579041+00:00
-- url     : https://prove2.me/theorems/6cdf2f18-6aa8-4795-9fe8-ce29ad7da79d
-- title:
--   Matrix Gaussian: gaussian diagonal
-- statement:
--   The Matrix Gaussian construction uses the gaussian diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L69-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L69-L84

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

theorem GlobalTheory.MatrixGaussian.gaussian_diagonal (d : ι → ℂ) (hd : ∀ i, 0 < (d i).re) :
    Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z))) ∧
      ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = (diagonal d).det⁻¹ := by sorry
