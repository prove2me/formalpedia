-- Prove2me | Theorems.Thm_GlobalTheory_subst_eq_of_coeff_eq_of_killed
-- name    : GlobalTheory.subst_eq_of_coeff_eq_of_killed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:26:49.623984+00:00
-- url     : https://prove2.me/theorems/b89962e5-ccdc-47e5-b4c2-11b651c4c3c8
-- title:
--   Global Theory: subst eq of coeff eq of killed
-- statement:
--   The Global Theory construction uses the subst eq of coeff eq of killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SubstEqOfCoeffEqOfKilled.lean#L5-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SubstEqOfCoeffEqOfKilled.lean#L5-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SubstEqOfCoeffEqOfKilled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.subst_eq_of_coeff_eq_of_killed :
    ∀ (C : Type) [Field C] (σ τ : Type) [Fintype σ] [Fintype τ] (P : σ → Prop) (f : σ → MvPowerSeries τ C) (F F' : MvPowerSeries σ C), (∀ w, MvPowerSeries.constantCoeff (f w) = 0) → (∀ w, ¬ P w → f w = 0) → (∀ μ : σ →₀ ℕ, (∀ w ∈ μ.support, P w) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F') → MvPowerSeries.subst f F = MvPowerSeries.subst f F' := by sorry
