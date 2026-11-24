-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedCoord_dirDeriv_mul
-- name    : GlobalTheory.AdaptedCoord.dirDeriv_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:16.928009+00:00
-- url     : https://prove2.me/theorems/e13b71c8-044c-4871-ae5c-56ca4bf44439
-- title:
--   Adapted Coord: dir Deriv mul
-- statement:
--   The Adapted Coord construction uses the dir Deriv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FderivEqZeroOfAffine.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/FderivEqZeroOfAffine.lean#L63-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AdaptedCoord
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem GlobalTheory.AdaptedCoord.dirDeriv_mul {U : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) (f f' : Γ(A.left, U)) :
    dirDeriv u h w (f * f') =
      valAt' (u.ex 0).left U f * dirDeriv u h w f' + valAt' (u.ex 0).left U f' * dirDeriv u h w f := by sorry
