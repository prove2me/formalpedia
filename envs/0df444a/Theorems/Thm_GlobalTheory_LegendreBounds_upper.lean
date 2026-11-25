-- Prove2me | Theorems.Thm_GlobalTheory_LegendreBounds_upper
-- name    : GlobalTheory.LegendreBounds.upper
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:24.582315+00:00
-- url     : https://prove2.me/theorems/893b9add-4e03-4366-ae84-dfa03a452344
-- title:
--   Legendre Bounds: upper
-- statement:
--   The Legendre Bounds construction uses the upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L63-L70

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

theorem GlobalTheory.LegendreBounds.upper (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) ≤ (N : ℝ) / (l - 1) := by sorry
