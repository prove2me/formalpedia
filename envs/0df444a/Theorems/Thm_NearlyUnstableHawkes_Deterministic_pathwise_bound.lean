-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_pathwise_bound
-- name    : NearlyUnstableHawkes.Deterministic.pathwise_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:21.006518+00:00
-- url     : https://prove2.me/theorems/1dd6114d-1b51-4853-b311-60e7191d82bf
-- title:
--   §4.1, p. 14 — normalized fluctuations bounded by Mᵀ
-- statement:
--   Let $S_T=\sup_{0\le t\le T}|M_t^T|$. Under Assumption 1, almost surely, for every $v\in[0,1]$,
--
--   $$\frac{1-a_T}{T}\left|N^T_{Tv}-\mathbb E[N^T_{Tv}]\right|\le\frac{1-a_T}{T}(1+\|\psi^T\|_1)S_T\le\frac{S_T}{T}.$$
--
--   This pointwise bound is the bridge from the resolvent representation to the maximal-martingale estimate.
--
--   **Formalization Note** The first absolute value is omitted in the printed display on p. 14, but is needed by its following squared supremum. The Lean statement includes it.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 14, §4.1, “we deduce” display (absolute-value correction)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory

/-- Jaisson–Rosenbaum, §4.1, p. 14, corrected absolute-value bound. -/
theorem pathwise_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T μ a m : ℝ) (φ φ' : ℝ → ℝ) (N : ℝ → Ω → ℕ)
    (hT : 0 < T) (hμ : 0 < μ) (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : KernelAssumption φ φ' m)
    (hN : IsHawkes P μ (scaledKernel a φ) T N) :
    ∀ᵐ ω ∂P, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal ((1 - a) / T *
        |(N (T * v) ω : ℝ) - (∫ ω', (N (T * v) ω' : ℝ) ∂P)|) ≤
      ENNReal.ofReal ((1 - a) / T * (1 + psiNorm (scaledKernel a φ))) *
        martingaleMax μ (scaledKernel a φ) N T ω ∧
      ENNReal.ofReal ((1 - a) / T * (1 + psiNorm (scaledKernel a φ))) *
        martingaleMax μ (scaledKernel a φ) N T ω ≤
      ENNReal.ofReal (1 / T) * martingaleMax μ (scaledKernel a φ) N T ω := by sorry

end NearlyUnstableHawkes.Deterministic
