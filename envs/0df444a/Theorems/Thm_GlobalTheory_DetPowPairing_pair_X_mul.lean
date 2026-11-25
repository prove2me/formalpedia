-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_pair_X_mul
-- name    : GlobalTheory.DetPowPairing.pair_X_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:33:13.138255+00:00
-- url     : https://prove2.me/theorems/69fdb056-1d43-4e8f-823f-dd8161bfaac3
-- title:
--   Det Pow Pairing: pair X mul
-- statement:
--   The Det Pow Pairing construction uses the pair X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L63-L70

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
noncomputable section
open GlobalTheory GlobalTheory.DetPowPairing
open MvPolynomial
variable {σ : Type} {C : Type} [CommRing C]

theorem GlobalTheory.DetPowPairing.pair_X_mul (j : σ) (P Q : MvPolynomial σ C) :
    pair (P * X j) Q = pair P (pderiv j Q) := by sorry
