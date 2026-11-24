-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_det_ne_zero
-- name    : GlobalTheory.RiemannRel.det_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:09.879441+00:00
-- url     : https://prove2.me/theorems/7d4a8b4a-de7e-4f18-9f71-c50a293272ec
-- title:
--   Riemann Rel: det ne zero
-- statement:
--   The Riemann Rel construction uses the det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L36-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L36-L84

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

theorem GlobalTheory.RiemannRel.det_ne_zero (G A B : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * B.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    A.det ≠ 0 := by sorry
