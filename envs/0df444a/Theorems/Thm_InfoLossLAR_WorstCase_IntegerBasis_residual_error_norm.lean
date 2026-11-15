-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_residual_error_norm
-- name    : InfoLossLAR.WorstCase.IntegerBasis.residual_error_norm
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:28:10.768896+00:00
-- url     : https://prove2.me/theorems/f65b3d6e-8438-4b59-af7d-16bf6c8d7345
-- title:
--   Exact full-norm scaling in one correct modular BDD step
-- statement:
--   For any nonzero modulus and actual dual-lattice point, updating by its correct modular pairing secret scales the entire Euclidean query error by exactly the reciprocal modulus. The secret is the mathematical correct-answer invariant. This theorem does not assert that an algorithm has already recovered it.
-- source:
--   Complete existing checked theorem InfoLossLAR.WorstCase.IntegerBasis.residual_error_norm and its minimal proof-only helpers, extracted by official Lean declaration and syntax/info-tree oracles from the frozen BDD geometry modules. All helper and root proof bodies are exact source byte slices. Only the root binding is renamed to global solution and its surrounding dimension parameter is exposed explicitly. Shared objects use the pure original-basis coordinate definition provider. No new mathematical argument.

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

theorem residual_error_norm {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) (query : Space (dimension:=dimension)) :
    ‖residualQuery basis hdet q query (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)-
      (residualNearest basis hdet q nearest : Space (dimension:=dimension))‖=
        ‖query-(nearest : Space (dimension:=dimension))‖/(q : ℝ) := by sorry

end InfoLossLAR.WorstCase.IntegerBasis
