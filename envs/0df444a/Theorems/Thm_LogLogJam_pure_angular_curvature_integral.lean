-- Prove2me | Theorems.Thm_LogLogJam_pure_angular_curvature_integral
-- name    : LogLogJam.pure_angular_curvature_integral
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:14:14.697427+00:00
-- url     : https://prove2.me/theorems/63d87ead-5270-4b3c-8dfa-df6cb6a04fd4
-- title:
--   Exact mean angular Fisher curvature for any pure Gaussian seed
-- statement:
--   For any strictly squeezed state, positive integer copy count and positive-definite symplectic seed covariance W, the half-turn integral of one half the trace pairing of the inverse total covariance with its angular acceleration equals kπ(4E−2). The squeezed covariance is the tensor product of the common one-mode covariance with the identity on k modes. The result includes arbitrary correlations between seed modes.
-- source:
--   https://arxiv.org/abs/2607.12983, Lemma 6.1 and its pure seed equality case.

import Definitions.Def_LogLogJam_Obs
open Matrix MeasureTheory
open scoped Kronecker

namespace LogLogJam

theorem pure_angular_curvature_integral (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Matrix (Q k) (Q k) ℝ) (hpd : W.PosDef) (hs : W * Omega k * W = Omega k) :
    let D := fun θ => VsqK lam θ k + W
    let A := fun θ : ℝ => ((2*(lam-lam⁻¹)) • (rot θ * !![-1,0;0,1] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, ((D θ)⁻¹ * A θ).trace / 2
    I = k * Real.pi * (4 * energy lam - 2) := by sorry

end LogLogJam
