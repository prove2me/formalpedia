-- Prove2me | Theorems.Thm_GlobalTheory_DetPowPairing_main
-- name    : GlobalTheory.DetPowPairing.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:16.561673+00:00
-- url     : https://prove2.me/theorems/5c3de8fb-b31d-4d31-b1e8-d6b2a80fea82
-- title:
--   Det Pow Pairing: main
-- statement:
--   The Det Pow Pairing construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L117-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WtAddSingle.lean#L117-L122

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

theorem GlobalTheory.DetPowPairing.main :
    (∀ (C : Type) [Field C] [CharZero C] (n₀ x : ℕ), (∏ c ∈ Finset.range n₀, (c.factorial : C)) * (∑ A ∈ (cayDet n₀ C ^ x).support, MvPolynomial.coeff A (cayDet n₀ C ^ x) * (A.prod fun _ e => (e.factorial : C)) * MvPolynomial.coeff A (cayDet n₀ C ^ x)) = ∏ c ∈ Finset.range n₀, ((x + c).factorial : C)) := by sorry
