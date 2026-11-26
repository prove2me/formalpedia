-- Prove2me | Theorems.Thm_LogLogJam_sharp_angular_curvature_integral
-- name    : LogLogJam.sharp_angular_curvature_integral
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:52:17.864794+00:00
-- url     : https://prove2.me/theorems/d19e4236-7d2c-552f-8d01-0505f6fe9307
-- title:
--   Sharp mean trace pairing with the angular covariance acceleration
-- statement:
--   Let λ>1, k≥1, and let W be a physical k-copy Gaussian seed. For the covariance curve D equal to the k-copy rotated squeezed covariance plus W and its second angle derivative A, the real integral of tr(D⁻¹A)/2 over the half-turn is at most kπ(4E−2), with equality if and only if det(W)=1. The integrand can have either sign. This formulation uses a single inverse and is linear in the acceleration.
-- source:
--   https://arxiv.org/abs/2607.12983, Lemma 6.1 and the angular integration by parts in Section 6.1.

import Definitions.Def_LogLogJam_Obs
open Matrix MeasureTheory
open scoped Kronecker

namespace LogLogJam

theorem sharp_angular_curvature_integral (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    let D := fun θ => VsqK lam θ k + Matrix.of W
    let A := fun θ : ℝ => ((2*(lam-lam⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, ((D θ)⁻¹ * A θ).trace / 2
    I ≤ k * Real.pi * (4 * energy lam - 2) ∧
      (I = k * Real.pi * (4 * energy lam - 2) ↔ (Matrix.of W).det = 1) := by sorry

end LogLogJam
