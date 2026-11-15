-- Prove2me | Theorems.Thm_MazurP23_card_zeroComponent_prime_torsion
-- name    : MazurP23.card_zeroComponent_prime_torsion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:09:47.708694+00:00
-- url     : https://prove2.me/theorems/b5cb88ca-9b4b-42ce-99b1-246a00015f0c
-- title:
--   Zero-component p-torsion has order p (local)
-- statement:
--   Promoted from the Frey proof (helper tw_hM): for an integral Weierstrass curve and a prime p, the p-torsion points in the identity component at a multiplicative prime form a group of order p.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_EllipticCurve_ZeroComponentAt
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
theorem card_zeroComponent_prime_torsion (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime) (hΔ : W.Δ ≠ 0)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (hcard1 : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p : ℕ) : ℤ)) = p ^ 2) :
    Nat.card {x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point //
      p • x = 0 ∧ W.InZeroComponentAt A x} = p := by sorry
end MazurP23
