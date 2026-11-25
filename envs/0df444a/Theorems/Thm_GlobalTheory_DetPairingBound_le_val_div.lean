-- Prove2me | Theorems.Thm_GlobalTheory_DetPairingBound_le_val_div
-- name    : GlobalTheory.DetPairingBound.le_val_div
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:38:43.979809+00:00
-- url     : https://prove2.me/theorems/ff99af81-19af-4618-aa66-121ede70e1a3
-- title:
--   Det Pairing Bound: le val div
-- statement:
--   The Det Pairing Bound construction uses the le val div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DeterminantPairingQuotientValuationLowerBound.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DeterminantPairingQuotientValuationLowerBound.lean#L38-L48

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.DetPairingBound
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

theorem GlobalTheory.DetPairingBound.le_val_div {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {N D : C} {a d r : ℝ}
    (hN : (a : WithTop ℝ) ≤ v N) (hD : v D = d) (h : r ≤ a - d) : (r : WithTop ℝ) ≤ v (N / D) := by sorry
