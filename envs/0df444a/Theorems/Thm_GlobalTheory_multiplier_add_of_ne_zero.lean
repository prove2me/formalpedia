-- Prove2me | Theorems.Thm_GlobalTheory_multiplier_add_of_ne_zero
-- name    : GlobalTheory.multiplier_add_of_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:15.960865+00:00
-- url     : https://prove2.me/theorems/3ed926a1-1aec-42ac-9226-c342a8cc1683
-- title:
--   Global Theory: multiplier add of ne zero
-- statement:
--   The Global Theory construction uses the multiplier add of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L494-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L494-L518

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}

theorem GlobalTheory.multiplier_add_of_ne_zero (hτ : τ.IsSymm) {χ : (ι → ℤ) → (ι → ℤ) → ℂ} (hf : f ≠ 0)
    (h : ∀ (n n' : ι → ℤ) (z : ι → ℂ), f (z + τ *ᵥ ofIntVec n + ofIntVec n') = χ n n' *
      eC (-(N : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * f z)
    (n n' m m' : ι → ℤ) : χ (n + m) (n' + m') = χ n n' * χ m m' := by sorry
