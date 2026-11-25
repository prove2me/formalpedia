-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_pair_det
-- name    : GlobalTheory.DetPowPairing.pair_det
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:32:57.566751+00:00
-- url     : https://prove2.me/theorems/e88d7dec-f5f3-4f4b-8c8c-34f5325cf680
-- title:
--   Det Pow Pairing: pair det
-- statement:
--   The Det Pow Pairing construction uses the pair det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L82-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L82-L93

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

theorem GlobalTheory.DetPowPairing.pair_det (n : ℕ) (P Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * cayDet n C) Q = pair P (cayOp n C Q) := by sorry
