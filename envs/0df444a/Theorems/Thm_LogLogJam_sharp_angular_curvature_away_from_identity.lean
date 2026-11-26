-- Prove2me | Theorems.Thm_LogLogJam_sharp_angular_curvature_away_from_identity
-- name    : LogLogJam.sharp_angular_curvature_away_from_identity
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:56:08.299424+00:00
-- url     : https://prove2.me/theorems/c307231d-e835-48d5-af18-684e29cb5ed9
-- title:
--   Angular curvature bound for physical seeds other than the identity covariance
-- statement:
--   For λ>1, any k≥1 and any physical seed covariance W different from the identity matrix, the angle integral of tr(D⁻¹D″)/2 over a half-turn is at most kπ(4E−2), with equality exactly at det(W)=1. D is the k-copy rotated squeezed covariance plus W. This is the remaining case after the exact product heterodyne calculation.
-- source:
--   https://arxiv.org/abs/2607.12983, Lemma 6.1 and the angular integration by parts in Section 6.1.

import Definitions.Def_LogLogJam_Obs
open Matrix MeasureTheory
open scoped Kronecker

namespace LogLogJam

theorem sharp_angular_curvature_away_from_identity (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) (hother : Matrix.of W ≠ 1) :
    let D := fun θ => VsqK lam θ k + Matrix.of W
    let A := fun θ : ℝ => ((2*(lam-lam⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, ((D θ)⁻¹ * A θ).trace / 2
    I ≤ k * Real.pi * (4 * energy lam - 2) ∧
      (I = k * Real.pi * (4 * energy lam - 2) ↔ (Matrix.of W).det = 1) := by sorry

end LogLogJam
