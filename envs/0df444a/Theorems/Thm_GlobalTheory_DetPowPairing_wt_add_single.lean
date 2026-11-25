-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_wt_add_single
-- name    : GlobalTheory.DetPowPairing.wt_add_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:34:17.345787+00:00
-- url     : https://prove2.me/theorems/54c71799-436e-452a-9380-877d9ad3a369
-- title:
--   Det Pow Pairing: wt add single
-- statement:
--   The Det Pow Pairing construction uses the wt add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L34-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L34-L57

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

theorem GlobalTheory.DetPowPairing.wt_add_single (A : σ →₀ ℕ) (j : σ) :
    wt C (A + Finsupp.single j 1) = wt C A * ((A j : C) + 1) := by sorry
