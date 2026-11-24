-- Prove2me | Theorems.Thm_GlobalTheory_ColLie_hasDerivAt_coeff_mul_X
-- name    : GlobalTheory.ColLie.hasDerivAt_coeff_mul_X
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:44.551179+00:00
-- url     : https://prove2.me/theorems/b47a3b9e-9219-4284-9076-a0509f2d8fba
-- title:
--   Col Lie: has Deriv At coeff mul X
-- statement:
--   The Col Lie construction uses the has Deriv At coeff mul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L31-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtCoeffFockColumnSubstitutionExp.lean#L31-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtCoeffFockColumnSubstitutionExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]

theorem GlobalTheory.ColLie.hasDerivAt_coeff_mul_X {σ : Type} {A : ℝ → MvPolynomial σ ℂ} {B : MvPolynomial σ ℂ}
    (hA : ∀ m, HasDerivAt (fun h => coeff m (A h)) (coeff m B) 0) (w : σ) (m : σ →₀ ℕ) :
    HasDerivAt (fun h => coeff m (A h * X w)) (coeff m (B * X w)) 0 := by sorry
