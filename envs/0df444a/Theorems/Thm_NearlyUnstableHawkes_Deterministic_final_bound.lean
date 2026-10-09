-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_final_bound
-- name    : NearlyUnstableHawkes.Deterministic.final_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:13.427392+00:00
-- url     : https://prove2.me/theorems/60bf773e-de15-4105-a21f-b62085881924
-- title:
--   §4.1, p. 15 — finite-horizon L² fluctuation bound
-- statement:
--   Under Assumption 1, at a fixed observation horizon $T>0$ with $0<a_T<1$, the normalized fluctuations satisfy
--
--   $$\mathbb E\!\left[\left(\sup_{v\in[0,1]}\frac{1-a_T}{T}\left|N^T_{Tv}-\mathbb E[N^T_{Tv}]\right|\right)^2\right]\le\frac{4\mu}{T(1-a_T)}.$$
--
--   This is the quantitative estimate from which Theorem 2.1 follows when $T(1-a_T)\to\infty$.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 15, §4.1, “Therefore, we finally obtain” display

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, §4.1, p. 15, final finite-`T` estimate. -/
theorem final_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T μ a m : ℝ) (φ φ' : ℝ → ℝ) (N : ℝ → Ω → ℕ)
    (hT : 0 < T) (hμ : 0 < μ) (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hN : IsHawkes P μ (scaledKernel a φ) T N) :
    (∫⁻ ω, (scaledDeviation a T N P ω) ^ 2 ∂P) ≤
      ENNReal.ofReal (4 * μ / (T * (1 - a))) := by sorry

end NearlyUnstableHawkes.Deterministic
