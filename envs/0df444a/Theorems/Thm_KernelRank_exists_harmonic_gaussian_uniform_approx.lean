-- Prove2me | Theorems.Thm_KernelRank_exists_harmonic_gaussian_uniform_approx
-- name    : KernelRank.exists_harmonic_gaussian_uniform_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:44:54.166302+00:00
-- url     : https://prove2.me/theorems/30d5aef1-0330-4ec4-b585-be0d4d09737a
-- title:
--   Kernel Rank: exists harmonic gaussian uniform approx
-- statement:
--   **Equal-width harmonic complex-Gaussian universal approximation on `ℝ^d` (`d ≥ 2`).**
--   For every continuous radial profile `ψ : ℝ → ℝ` on `[0, ∞)` with `lim_{s → ∞} ψ(s) = 0`, every
--   shared decay parameter `α > 0`, and every tolerance `ε > 0`, there exist a fundamental frequency
--   `ω₀ > 0`, a harmonic count `M`, a real DC Gaussian weight `a₀`, and complex harmonic weights
--   `a₁, …, a_M` such that the equal-width harmonic multi-Gaussian kernel
--   `x ↦ a₀ exp(-α ‖x‖²) + ∑_{m=1}^M Re (a_m exp((-α + i m ω₀) ‖x‖²))`
--   has `d`-way real separable rank at most `1 + d M` and approximates `x ↦ ψ(‖x‖²)` uniformly
--   within `ε` across *all* of `ℝ^d`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L872-L1180
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Approximation.lean#L872-L1180

import Definitions.Def_KernelRankLean_Main
import Definitions.Def_KernelRankLean_Approximation
set_option autoImplicit true
open Complex Polynomial
open scoped Topology
open KernelRank

theorem KernelRank.exists_harmonic_gaussian_uniform_approx {d : ℕ} (hd : 2 ≤ d)
    {ψ : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Set.Ici 0))
    (hψ_zero : Filter.Tendsto ψ Filter.atTop (𝓝 0))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ω₀ : ℝ) (M : ℕ) (a₀ : ℝ) (a : Fin M → ℂ),
      0 < ω₀ ∧
      separableRank (fun x : Fin d → ℝ =>
        a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
          ∑ m : Fin M,
            (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) * (∑ j, x j ^ 2 : ℝ))).re) ≤
        (1 + d * M : ℕ) ∧
      ∀ x : Fin d → ℝ,
        |(a₀ * Real.exp (-α * ∑ j, x j ^ 2) +
            ∑ m : Fin M,
              (a m * exp (((-α : ℝ) + I * (((m : ℕ) + 1 : ℝ) * ω₀)) *
                (∑ j, x j ^ 2 : ℝ))).re) -
          ψ (∑ j, x j ^ 2)| < ε := by sorry
