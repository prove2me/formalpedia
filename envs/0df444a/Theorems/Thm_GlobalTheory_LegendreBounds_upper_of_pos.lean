-- Prove2me | Theorems.Thm_GlobalTheory_LegendreBounds_upper_of_pos
-- name    : GlobalTheory.LegendreBounds.upper_of_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:14.29475+00:00
-- url     : https://prove2.me/theorems/6f9c8ba7-8f64-40b2-8c4d-fef13d84ea15
-- title:
--   Legendre Bounds: upper of pos
-- statement:
--   The Legendre Bounds construction uses the upper of pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L72-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L72-L85

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.LegendreBounds

theorem GlobalTheory.LegendreBounds.upper_of_pos (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : 1 ≤ N) :
    (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / (l - 1) := by sorry
