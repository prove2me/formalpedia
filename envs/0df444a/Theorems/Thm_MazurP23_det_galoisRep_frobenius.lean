-- Prove2me | Theorems.Thm_MazurP23_det_galoisRep_frobenius
-- name    : MazurP23.det_galoisRep_frobenius
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:09:49.544971+00:00
-- url     : https://prove2.me/theorems/c7ca3a5a-73e6-447b-99fd-ae98da6346ad
-- title:
--   Determinant at a Frobenius is q mod p
-- statement:
--   Promoted from the Frey proof (helper tw_det_frob): for a Frobenius element at a prime q different from p, det of the mod p representation is q mod p.
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open CuspForm ModularFormClass UpperHalfPlane

namespace MazurP23
theorem det_galoisRep_frobenius (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (hΔ : W.Δ ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ q) :
    LinearMap.det (WeierstrassCurve.Affine.Point.galoisRepModuleEnd
        (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p σ)
      = ((q : ℕ) : ZMod p) := by sorry
end MazurP23
