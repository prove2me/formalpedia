-- Prove2me | Theorems.Thm_LogLogJam_sharp_angular_trace_integral
-- name    : LogLogJam.sharp_angular_trace_integral
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-26T09:47:59.243352+00:00
-- url     : https://prove2.me/theorems/8da4e708-1408-5e01-b6a5-47d0b74afbdb
-- title:
--   Sharp angular trace integral for a strictly squeezed covariance and a physical seed
-- statement:
--   For a strictly squeezed input (λ>1), any positive integer batch size k, and any physical Gaussian seed W, let D be the sum of the rotated squeezed input covariance and W, and H its angle derivative. The ordinary real integral over one half-turn of half the trace of (D⁻¹H)² is at most kπ(4E−2). For strict squeezing equality holds exactly when det W=1.
-- source:
--   https://arxiv.org/abs/2607.12983, Lemma 6.1, Eqs. (68)–(74).

import Definitions.Def_LogLogJam_Obs
open Matrix MeasureTheory
open scoped Kronecker

namespace LogLogJam

theorem sharp_angular_trace_integral (lam : ℝ) (hlam : 1 < lam) (k : ℕ) (hk : 1 ≤ k)
    (W : Q k → Q k → ℝ) (hW : IsCov k (Matrix.of W)) :
    let D := fun θ => VsqK lam θ k + Matrix.of W
    let H := fun θ : ℝ => ((lam-lam⁻¹) • (rot θ * !![0,1;1,0] * (rot θ)ᵀ)) ⊗ₖ (1 : Matrix (Fin k) (Fin k) ℝ)
    let I := ∫ θ in Set.Ico 0 Real.pi, (((D θ)⁻¹ * H θ) * ((D θ)⁻¹ * H θ)).trace / 2
    I ≤ k * Real.pi * (4 * energy lam - 2) ∧
      (I = k * Real.pi * (4 * energy lam - 2) ↔ (Matrix.of W).det = 1) := by sorry

end LogLogJam
