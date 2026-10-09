-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Deterministic_theorem_2_1
-- name    : NearlyUnstableHawkes.Deterministic.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:30.976987+00:00
-- url     : https://prove2.me/theorems/4e31ec6a-f1d3-484e-a46c-35124264a295
-- title:
--   Theorem 2.1, p. 6 — asymptotic determinism in L²
-- statement:
--   Let $T_n\to\infty$ be observation horizons and let $a_n\in(0,1)$ tend to $1$. For each $n$, let $N^{T_n}$ be a Hawkes process with baseline rate $\mu>0$ and kernel $\phi^{T_n}=a_n\phi$, where $\phi$ satisfies Assumption 1. If $T_n(1-a_n)\to\infty$, then
--
--   $$\mathbb E\!\left[\left(\sup_{v\in[0,1]}\frac{1-a_n}{T_n}\left|N^{T_n}_{T_nv}-\mathbb E[N^{T_n}_{T_nv}]\right|\right)^2\right]\longrightarrow0.$$
--
--   Thus, throughout the unit observation interval, the normalized Hawkes count concentrates around its deterministic mean in $L^2$.
--
--   **Formalization Note** The index $n$ makes the paper's implicit sequence $T_n$ explicit. Each process may live on its own probability space. The pathwise supremum is represented in extended nonnegative reals, preserving an infinite value rather than assigning a real default. The mean is a Bochner integral; its integrability follows from the Hawkes hypotheses and is not assumed separately.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 6, Theorem 2.1

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Deterministic_Setting

namespace NearlyUnstableHawkes.Deterministic

open MeasureTheory Filter Topology

/-- Jaisson–Rosenbaum, Theorem 2.1, p. 6. -/
theorem theorem_2_1 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (μ m : ℝ) (φ φ' : ℝ → ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (ha : Tendsto a atTop (𝓝 1)) (hμ : 0 < μ)
    (hφ : KernelAssumption φ φ' m)
    (hN : ∀ n, IsHawkes (P n) μ (scaledKernel (a n) φ) (T n) (N n))
    (hregime : Tendsto (fun n => T n * (1 - a n)) atTop atTop) :
    Tendsto (fun n => ∫⁻ ω, (scaledDeviation (a n) (T n) (N n) (P n) ω) ^ 2 ∂P n)
      atTop (𝓝 0) := by sorry

end NearlyUnstableHawkes.Deterministic
