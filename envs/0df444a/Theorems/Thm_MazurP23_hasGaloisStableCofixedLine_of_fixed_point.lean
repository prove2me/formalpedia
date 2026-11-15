-- Prove2me | Theorems.Thm_MazurP23_hasGaloisStableCofixedLine_of_fixed_point
-- name    : MazurP23.hasGaloisStableCofixedLine_of_fixed_point
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-14T23:32:32.710638+00:00
-- url     : https://prove2.me/theorems/4a83a400-a8fc-45e1-b0c0-b3ae8c855689
-- title:
--   A rational p-torsion point gives a Galois-stable cofixed line
-- statement:
--   Under the same local hypotheses as MazurP23.not_hasGaloisStableCofixedLine_of_localData, a Galois-fixed point Q of order p that lies off the identity component at 2 and at 3 yields a Galois-stable cofixed line in E[p] (Mazur's step: the line spanned by Q has a stable complement).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ExtCitation_AdmissibleExtension
import Definitions.Def_ExtCitation_AdmissibleExtension_v2
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_ValuationSubring_ReduceAt
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
theorem hasGaloisStableCofixedLine_of_fixed_point
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
      ∨ ((p : ℤ) ∣ W.Δ ∧ ¬ (p : ℤ) ∣ W.c₄))
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p)
    (h2 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 → ¬ W.InZeroComponentAt A Q)
    (h3 : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 → ¬ W.InZeroComponentAt A Q) :
    HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ (W.map (Int.castRingHom ℚ)) p := by sorry
end MazurP23
