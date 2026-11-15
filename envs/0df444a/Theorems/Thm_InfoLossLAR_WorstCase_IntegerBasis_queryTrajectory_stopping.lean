-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_queryTrajectory_stopping
-- name    : InfoLossLAR.WorstCase.IntegerBasis.queryTrajectory_stopping
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:30:57.936648+00:00
-- url     : https://prove2.me/theorems/a8aab78c-6c1f-46f7-a924-d1aef1eef688
-- title:
--   A geometric exponent bound gives a bounded ideal BDD trajectory
-- statement:
--   Let q≥2. If the initial full query error is at most radius and radius times every original input-column norm is at most 2^K, then after K+2 ideal all-correct modular residual updates the full residual error times every column norm is strictly below one half. The trajectory is explicitly ideal and hidden-nearest-dependent for analysis; no algorithm gets that hidden point. The stopping count depends on the given geometric exponent K, and this theorem does not itself prove an LLL or BDD algorithm.
-- source:
--   Complete existing checked theorem InfoLossLAR.WorstCase.IntegerBasis.queryTrajectory_stopping and its minimal proof-only helpers, extracted by official Lean declaration and syntax/info-tree oracles from the frozen BDD geometry modules. All helper and root proof bodies are exact source byte slices. Only the root binding is renamed to global solution and its surrounding dimension parameter is exposed explicitly. Shared objects use the pure original-basis coordinate definition provider. No new mathematical argument.

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_residual_error_norm

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

theorem queryTrajectory_stopping {dimension : ℕ}
    (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (nearest : dual (inputLattice basis hdet)) (query : Space (dimension:=dimension))
    (radius : ℝ) (exponent : ℕ)
    (hquery : ‖query-(nearest : Space (dimension:=dimension))‖ ≤ radius)
    (hcolumns : ∀ index : Fin dimension,radius*‖(integerBasis basis hdet index : Space (dimension:=dimension))‖ ≤ (2 : ℝ)^exponent) :
    ∀ index : Fin dimension,
      ‖queryTrajectory basis hdet q nearest (exponent+2) query-
        (nearestTrajectory basis hdet q (exponent+2) nearest : Space (dimension:=dimension))‖*
        ‖(integerBasis basis hdet index : Space (dimension:=dimension))‖ < 1/2 := by sorry

end InfoLossLAR.WorstCase.IntegerBasis
