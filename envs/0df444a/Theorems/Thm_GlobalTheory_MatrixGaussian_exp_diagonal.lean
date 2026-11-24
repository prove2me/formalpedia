-- Prove2me | Theorems.Thm_GlobalTheory_MatrixGaussian_exp_diagonal
-- name    : GlobalTheory.MatrixGaussian.exp_diagonal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:21:15.0218+00:00
-- url     : https://prove2.me/theorems/3f60f330-774b-4061-82fd-4937c9d4c69e
-- title:
--   Matrix Gaussian: exp diagonal
-- statement:
--   The Matrix Gaussian construction uses the exp diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralComplexGaussianPosDefHermitianPart.lean#L61-L67

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

theorem GlobalTheory.MatrixGaussian.exp_diagonal (d z : ι → ℂ) :
    cexp (-(π : ℂ) * (star z ⬝ᵥ (diagonal d) *ᵥ z)) = ∏ i, cexp (-(π * d i) * (‖z i‖ : ℂ) ^ 2) := by sorry
