-- Prove2me | Theorems.Thm_GlobalTheory_LegendreBounds_digitSum_le
-- name    : GlobalTheory.LegendreBounds.digitSum_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:55.154168+00:00
-- url     : https://prove2.me/theorems/ca345ae1-cfe7-4c92-9ffe-3d5466b6dbab
-- title:
--   Legendre Bounds: digit Sum le
-- statement:
--   The Legendre Bounds construction uses the digit Sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LegendreBoundsFactorialMultiIndexCapelli.lean#L10-L20

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

theorem GlobalTheory.LegendreBounds.digitSum_le (l N : ℕ) (hl : 1 < l) :
    (Nat.digits l N).sum ≤ (Nat.log l N + 1) * (l - 1) := by sorry
