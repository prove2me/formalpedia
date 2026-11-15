-- Prove2me | Theorems.Thm_MazurP23_not_hasGaloisStableCofixedLine_of_localData
-- name    : MazurP23.not_hasGaloisStableCofixedLine_of_localData
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:09:57.407472+00:00
-- url     : https://prove2.me/theorems/e4a64fff-5c7a-475b-98de-fa9b3c35f2bf
-- title:
--   No Galois-stable cofixed line from local data (p >= 17)
-- statement:
--   Generalization of the Frey-curve theorem FreyPackage.frey_no_cofixed_large: an integral Weierstrass curve with multiplicative reduction at 2 and 3, and at every other prime q != p either good reduction, multiplicative reduction or inertia acting trivially on p-power torsion, and at p either good reduction with an integral p-torsion point above p or multiplicative reduction, has no Galois-stable cofixed line mod p for p >= 17. Proof adapted from anthropics/fermats-last-theorem (Apache-2.0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
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
theorem not_hasGaloisStableCofixedLine_of_localData
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp17 : 17 ≤ p)
    (h2Δ : (2:ℤ) ∣ W.Δ) (h2c₄ : ¬ (2:ℤ) ∣ W.c₄)
    (h3Δ : (3:ℤ) ∣ W.Δ) (h3c₄ : ¬ (3:ℤ) ∣ W.c₄)
    (hloc : ∀ q : ℕ, q.Prime → q ≠ p →
      ¬ (q : ℤ) ∣ W.Δ ∨ ((q : ℤ) ∣ W.Δ ∧ ¬ (q : ℤ) ∣ W.c₄) ∨
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q → ∀ τ ∈ A.inertiaSubgroupIn ℚ,
        ∀ (n : ℕ) (y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point), p ^ n • y = 0 → τ • y = y)
    (hpat : (¬ (p : ℤ) ∣ W.Δ ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∃ (x y : AlgebraicClosure ℚ)
          (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
          p • (Point.some x y h) = 0 ∧ x ∈ A)
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄)) :
    ¬ HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p := by sorry
end MazurP23
