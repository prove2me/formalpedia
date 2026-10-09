-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_mean_formula
-- name    : NearlyUnstableHawkes.Deterministic.mean_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:01.789681+00:00
-- url     : https://prove2.me/theorems/aaa30740-90c9-442a-a05f-6b93480720c5
-- title:
--   §4.1, p. 14 — mean of the Hawkes count
-- statement:
--   For a Hawkes process $N^T$ satisfying Assumption 1, write $\psi^T$ for the resolvent of $\phi^T=a_T\phi$. At every $v\in[0,1]$,
--
--   $$\mathbb E[N^T_{Tv}]=\mu Tv+\mu\int_0^{Tv}\psi^T(Tv-s)s\,ds.$$
--
--   This identifies the deterministic mean that is subtracted in Theorem 2.1.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 14, §4.1, first display

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, §4.1, p. 14, first display. -/
theorem mean_formula {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T μ a m : ℝ) (φ φ' : ℝ → ℝ) (N : ℝ → Ω → ℕ)
    (hT : 0 < T) (hμ : 0 < μ) (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hN : IsHawkes P μ (scaledKernel a φ) T N) :
    ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (∫ ω, (N (T * v) ω : ℝ) ∂P) =
        μ * (T * v) + μ * ∫ s in (0 : ℝ)..(T * v),
          psi (scaledKernel a φ) (T * v - s) * s := by sorry

end NearlyUnstableHawkes.Deterministic
