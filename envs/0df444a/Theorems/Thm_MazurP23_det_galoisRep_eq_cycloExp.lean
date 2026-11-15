-- Prove2me | Theorems.Thm_MazurP23_det_galoisRep_eq_cycloExp
-- name    : MazurP23.det_galoisRep_eq_cycloExp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:09:48.924212+00:00
-- url     : https://prove2.me/theorems/b9971a42-2598-499a-a6e3-5e07ea0c816a
-- title:
--   Determinant of the mod p Galois representation is cyclotomic
-- statement:
--   Promoted from the Frey proof (helper tw_det_eq_cyclo): det of the mod p representation of E[p] equals the mod p cyclotomic exponent character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_ExtCitation_AdmissibleExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23
theorem det_galoisRep_eq_cycloExp (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((ExtCitation.cycloExp p σ : ℕ) : ZMod p) := by sorry
end MazurP23
