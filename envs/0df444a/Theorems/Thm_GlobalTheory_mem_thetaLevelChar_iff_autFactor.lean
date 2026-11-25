-- Prove2me | Theorems.Thm_GlobalTheory_mem_thetaLevelChar_iff_autFactor
-- name    : GlobalTheory.mem_thetaLevelChar_iff_autFactor
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:37:24.557015+00:00
-- url     : https://prove2.me/theorems/66f25e4f-007f-40a8-9b4b-f1d67599a46e
-- title:
--   Global Theory: mem theta Level Char iff aut Factor
-- statement:
--   The Global Theory construction uses the mem theta Level Char iff aut Factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L60-L67

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

theorem GlobalTheory.mem_thetaLevelChar_iff_autFactor : f ∈ thetaLevelChar a b N τ ↔ Differentiable ℂ f ∧
    ∀ (n n' : ι → ℤ) (z : ι → ℂ), f (z + τ *ᵥ ofIntVec n + ofIntVec n') =
      autFactor a b τ n n' z ^ N * f z := by sorry
