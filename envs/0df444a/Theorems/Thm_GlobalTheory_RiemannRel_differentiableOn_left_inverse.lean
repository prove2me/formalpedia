-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_differentiableOn_left_inverse
-- name    : GlobalTheory.RiemannRel.differentiableOn_left_inverse
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:08:57.141306+00:00
-- url     : https://prove2.me/theorems/46ed15c1-19ca-4d93-ab38-2da0b7b1e746
-- title:
--   Riemann Rel: differentiable On left inverse
-- statement:
--   The Riemann Rel construction uses the differentiable On left inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L182-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L182-L199

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
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}

theorem GlobalTheory.RiemannRel.differentiableOn_left_inverse {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {B : Set V}
    (A h : V → Matrix (Fin g) (Fin g) ℂ) (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hh : ∀ b ∈ B, h b * A b = 1) (i j : Fin g) : DifferentiableOn ℂ (fun b => h b i j) B := by sorry
