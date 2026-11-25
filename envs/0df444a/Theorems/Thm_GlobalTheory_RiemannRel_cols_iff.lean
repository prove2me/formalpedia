-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_cols_iff
-- name    : GlobalTheory.RiemannRel.cols_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:07.040398+00:00
-- url     : https://prove2.me/theorems/5398b8a9-125a-5110-9261-b413cc31496b
-- title:
--   Riemann Rel: cols iff
-- statement:
--   The Riemann Rel construction uses the cols iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L209-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L209-L227

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}

theorem GlobalTheory.RiemannRel.cols_iff (h τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → Fin g → ℂ) :
    (∀ k, h *ᵥ a k = Pi.single k 1 ∧ h *ᵥ b k = τ *ᵥ Pi.single k 1) ↔
      h * (Matrix.of fun i j => a j i) = 1 ∧ τ = h * (Matrix.of fun i j => b j i) := by sorry
