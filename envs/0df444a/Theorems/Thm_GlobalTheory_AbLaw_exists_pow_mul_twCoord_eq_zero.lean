-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_exists_pow_mul_twCoord_eq_zero
-- name    : GlobalTheory.AbLaw.exists_pow_mul_twCoord_eq_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:53:54.824674+00:00
-- url     : https://prove2.me/theorems/4889a4ba-064f-428e-80d3-552f5aa01323
-- title:
--   Ab Law: exists pow mul tw Coord eq zero
-- statement:
--   The Ab Law construction uses the exists pow mul tw Coord eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNhdsPowMulTwCoordEqZero.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsNhdsPowMulTwCoordEqZero.lean#L48-L62

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

theorem GlobalTheory.AbLaw.exists_pow_mul_twCoord_eq_zero : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → ∀ a : SecOn (tw M H t) ⊤, SecOn.restrict _ (le_top : V ≤ ⊤) a = 0 → ∃ k : ℕ, ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_right.trans inf_le_right : ⊤ ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord a p l = 0 := by sorry
