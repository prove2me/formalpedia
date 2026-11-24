-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_isOpen_convex
-- name    : GlobalTheory.PeriodChart.isOpen_convex
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:09.993658+00:00
-- url     : https://prove2.me/theorems/26e41890-1496-45e8-966d-47956cde8694
-- title:
--   Period Chart: is Open convex
-- statement:
--   The Period Chart construction uses the is Open convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L542-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L542-L592

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]

theorem GlobalTheory.PeriodChart.isOpen_convex {m : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (Z : (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ) :
    IsOpen {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} ∧
    Convex ℝ {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} := by sorry
