-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_exists_nhds_pow_mul_twCoord_eq_zero
-- name    : GlobalTheory.AbLaw.exists_nhds_pow_mul_twCoord_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:34.861806+00:00
-- url     : https://prove2.me/theorems/aeff696a-a379-4e75-a6e2-88daa41da9c0
-- title:
--   Ab Law: exists nhds pow mul tw Coord eq zero
-- statement:
--   The Ab Law construction uses the exists nhds pow mul tw Coord eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNhdsPowMulTwCoordEqZero.lean#L13-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNhdsPowMulTwCoordEqZero.lean#L13-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNhdsPowMulTwCoordEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AbLaw

theorem GlobalTheory.AbLaw.exists_nhds_pow_mul_twCoord_eq_zero {Y : Scheme.{0}} {H M : LB Y} {d : ℤ}
    (σ : LB.Sec (pw H d)) {t : ℤ} (hH : H.IsLB) (hM : M.IsLB) (a : SecOn (tw M H t) ⊤)
    (ha : SecOn.restrict _ (le_top : nonzeroLocus σ ≤ ⊤) a = 0) (x : Y) :
    ∃ (W : Y.Opens) (n : ℕ), x ∈ W ∧ ∀ (p : M.ι) (l : H.ι) (O : Y.Opens) (_ : O ≤ W)
      (h : O ≤ ⊤ ⊓ (M.U p ⊓ H.U l)),
      rs Y (h.trans (inf_le_right.trans inf_le_right) : O ≤ H.U l) (σ.f l) ^ n *
        rs Y h (SecOn.twCoord a p l) = 0 := by sorry
