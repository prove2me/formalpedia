-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_centered_representation
-- name    : NearlyUnstableHawkes.Deterministic.centered_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:47.504481+00:00
-- url     : https://prove2.me/theorems/e5c62c70-962e-4b13-ba2f-7902c00bf51c
-- title:
--   §4.1, p. 14 — centered Hawkes count in terms of Mᵀ
-- statement:
--   Let $M_t^T=N_t^T-\int_0^t\lambda_s^T\,ds$ be the compensated process of a Hawkes process. Under Assumption 1, almost surely and simultaneously for every $v\in[0,1]$,
--
--   $$N^T_{Tv}-\mathbb E[N^T_{Tv}]=M^T_{Tv}+\int_0^{Tv}\psi^T(Tv-s)M_s^T\,ds.$$
--
--   This representation turns fluctuations of the count into fluctuations of its martingale component.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 14, §4.1, second display

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, §4.1, p. 14, second display. -/
theorem centered_representation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T μ a m : ℝ) (φ φ' : ℝ → ℝ) (N : ℝ → Ω → ℕ)
    (hT : 0 < T) (hμ : 0 < μ) (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hN : IsHawkes P μ (scaledKernel a φ) T N) :
    ∀ᵐ ω ∂P, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (N (T * v) ω : ℝ) - (∫ ω', (N (T * v) ω' : ℝ) ∂P) =
        compensated μ (scaledKernel a φ) N (T * v) ω +
          ∫ s in (0 : ℝ)..(T * v),
            psi (scaledKernel a φ) (T * v - s) *
              compensated μ (scaledKernel a φ) N s ω := by sorry

end NearlyUnstableHawkes.Deterministic
