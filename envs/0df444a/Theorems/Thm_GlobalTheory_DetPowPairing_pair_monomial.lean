-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_pair_monomial
-- name    : GlobalTheory.DetPowPairing.pair_monomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:29:54.110494+00:00
-- url     : https://prove2.me/theorems/e8be6427-aac4-455a-bac7-88ed18e95a15
-- title:
--   Det Pow Pairing: pair monomial
-- statement:
--   The Det Pow Pairing construction uses the pair monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L21-L26

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

theorem GlobalTheory.DetPowPairing.pair_monomial (A : σ →₀ ℕ) (c : C) (Q : MvPolynomial σ C) :
    pair (monomial A c) Q = c * wt C A * coeff A Q := by sorry
