-- Prove2me | Theorems.Thm_GlobalTheory_RiemannRel_hermForm_col
-- name    : GlobalTheory.RiemannRel.hermForm_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:58.761512+00:00
-- url     : https://prove2.me/theorems/e81dc96a-a2b2-4b88-a80b-18742c7d0fdd
-- title:
--   Riemann Rel: herm Form col
-- statement:
--   The Riemann Rel construction uses the herm Form col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableOnLeftInverse.lean#L28-L30

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

theorem GlobalTheory.RiemannRel.hermForm_col (G A B : Matrix (Fin g) (Fin g) ℂ) (j k : Fin g) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ Pi.single j 1) (B *ᵥ Pi.single k 1) = (Aᵀ * G * B.map (starRingEnd ℂ)) j k := by sorry
