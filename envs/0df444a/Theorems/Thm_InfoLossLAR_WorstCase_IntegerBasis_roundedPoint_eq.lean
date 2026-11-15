-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_roundedPoint_eq
-- name    : InfoLossLAR.WorstCase.IntegerBasis.roundedPoint_eq
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:17:28.995221+00:00
-- url     : https://prove2.me/theorems/514704b2-f2e2-4888-a366-ec7340bf53b7
-- title:
--   Exact original-dual point recovery by rational coordinate rounding
-- statement:
--   If the full Euclidean query error times each original input-column norm is strictly less than one half, the actual rational-coordinate nearest-integer reconstruction equals the specified genuine dual-lattice point. The hypothesis controls the complete error norm, not merely individual coordinate approximations. This is an exact stopping/recovery identity and supplies neither a BDD oracle nor its success guarantee.
-- source:
--   Complete existing checked theorem InfoLossLAR.WorstCase.IntegerBasis.roundedPoint_eq and its minimal proof-only helpers, extracted by official Lean declaration and syntax/info-tree oracles from the frozen BDD geometry modules. All helper and root proof bodies are exact source byte slices. Only the root binding is renamed to global solution and its surrounding dimension parameter is exposed explicitly. Shared objects use the pure original-basis coordinate definition provider. No new mathematical argument.

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

theorem roundedPoint_eq {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (nearest : dual (inputLattice basis hdet))
    (hsmall : ∀ index : Fin dimension,
      ‖rationalPoint query-(nearest : Space (dimension:=dimension))‖*
        ‖(integerBasis basis hdet index : Space (dimension:=dimension))‖ < 1/2) :
    roundedPoint basis hdet query=nearest := by sorry

end InfoLossLAR.WorstCase.IntegerBasis
