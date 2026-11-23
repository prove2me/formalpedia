-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_hermForm_mulVec
-- name    : GlobalTheory.RiemannRel.hermForm_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:22.792369+00:00
-- url     : https://prove2.me/theorems/f33e2e17-5893-40bf-a780-58101da91125
-- title:
--   Riemann Rel: herm Form mul Vec
-- statement:
--   The Riemann Rel construction uses the herm Form mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L17-L23

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

theorem GlobalTheory.RiemannRel.hermForm_mulVec (G A B : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ v) (B *ᵥ w) = v ⬝ᵥ (Aᵀ * G * B.map (starRingEnd ℂ)) *ᵥ star w := by sorry
