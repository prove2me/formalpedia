-- Prove2me | Theorems.Thm_GlobalTheory_norm_prod_sum_theta_le_exp
-- name    : GlobalTheory.norm_prod_sum_theta_le_exp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:49:10.341717+00:00
-- url     : https://prove2.me/theorems/40f22c92-111d-4b42-bce8-58c6909d47e6
-- title:
--   Global Theory: norm prod sum theta le exp
-- statement:
--   The Global Theory construction uses the norm prod sum theta le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/NormProdSumThetaLeExp.lean#L30-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/NormProdSumThetaLeExp.lean#L30-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NormProdSumThetaLeExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory

theorem GlobalTheory.norm_prod_sum_theta_le_exp :
    TStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : PT E) (DF : ℕ) (P : Par X DF) (r1 : ℕ), 2 ≤ r1 → ∀ s ∈ X.Sec 1 1, s ≠ 0 → ∀ (i Nc M : ℕ), 1 ≤ Nc → M ≤ r1 ^ (2 * PT.f E * X.r ^ 2) → ∀ (c z : Fin (2 * r1 ^ 4 * i) → Fin M → ℂ) (a : Fin (2 * r1 ^ 4 * i) → Fin M → Fin X.r → Vsp X.dim), (∀ k t, ‖c k t‖ ≤ Nc) → (∀ k t, (∀ j, ((r1 : ℂ) ^ 2) • a k t j ∈ X.L) ∧ ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L, x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a k t j) + (r1 : ℂ) • y) → (∀ k t, ‖z k t‖ ≤ ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a k t j) / Real.sqrt (X.l2 1 s)) → ‖∏ k, ∑ t, c k t * z k t‖ ≤ Real.exp (-(i * (P.ph - (2 * (r1 : ℝ) ^ 4 * (P.p3 + (Real.log Nc + 2 * PT.f E * (X.r : ℝ) ^ 2 * Real.log r1)) + ((r1 : ℝ) ^ 4 * X.r * dstar (E := E) P.m / 2) * Real.log (((r1 : ℝ) ^ 4 * X.r * dstar (E := E) P.m / 2) * P.ka0))))) := by sorry
