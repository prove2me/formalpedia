-- Prove2me | Theorems.Thm_GlobalTheory_MinorInt_lintegral_mul_right
-- name    : GlobalTheory.MinorInt.lintegral_mul_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:25:34.282763+00:00
-- url     : https://prove2.me/theorems/4e15723b-ba8b-4633-bd89-939a47d57bfc
-- title:
--   Minor Int: lintegral mul right
-- statement:
--   The Minor Int construction uses the lintegral mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L230-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/LintegralMulRight.lean#L230-L253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_LintegralMulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex MeasureTheory
open scoped ComplexConjugate ComplexOrder MatrixOrder
open GlobalTheory GlobalTheory.MinorInt

theorem GlobalTheory.MinorInt.lintegral_mul_right {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (hA : A.det ≠ 0) (F : (κ → ι → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ c, F c = ∫⁻ z : κ → ι → ℂ, ENNReal.ofReal (‖A.det‖ ^ (2 * Fintype.card κ)) *
      F (fun k => z k ᵥ* A) := by sorry
