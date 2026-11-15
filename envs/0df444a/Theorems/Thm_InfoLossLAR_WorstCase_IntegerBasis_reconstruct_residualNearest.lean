-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_IntegerBasis_reconstruct_residualNearest
-- name    : InfoLossLAR.WorstCase.IntegerBasis.reconstruct_residualNearest
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:19:39.667406+00:00
-- url     : https://prove2.me/theorems/f28b6e73-e788-4537-ad8f-c2f0359727a8
-- title:
--   Exact reconstruction from one correct modular residue and residual point
-- statement:
--   For every nonzero modulus, the explicit public reconstruction from the correct modular pairing residues and the genuine residual nearest point returns the original dual-lattice point exactly. This is an algebraic identity, without an algorithmic oracle-success assertion.
-- source:
--   Complete existing checked theorem InfoLossLAR.WorstCase.IntegerBasis.reconstruct_residualNearest and its minimal proof-only helpers, extracted by official Lean declaration and syntax/info-tree oracles from the frozen BDD geometry modules. All helper and root proof bodies are exact source byte slices. Only the root binding is renamed to global solution and its surrounding dimension parameter is exposed explicitly. Shared objects use the pure original-basis coordinate definition provider. No new mathematical argument.

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

namespace InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

theorem reconstruct_residualNearest {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    reconstructPoint basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)
      (residualNearest basis hdet q nearest : Space (dimension:=dimension))=(nearest : Space (dimension:=dimension)) := by sorry

end InfoLossLAR.WorstCase.IntegerBasis
