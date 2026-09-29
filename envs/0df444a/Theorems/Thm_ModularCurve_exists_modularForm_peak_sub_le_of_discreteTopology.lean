-- Prove2me | Theorems.Thm_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology
-- name    : ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/5e933ba6-b90b-5058-addf-99fa87cbb76f
-- title:
--   Peaked Poincaré series with geometric tail bound
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$, carrying the discrete topology as a subspace, and assume that no point $c$ of the boundary $\mathbb{R}\cup\{\infty\}$ (the one-point compactification `OnePoint ℝ`) satisfies `IsCusp c Γ`. Fix two points $\tau_0,\sigma_0$ of the upper half-plane $\mathbb{H}$. Then there are an open set $U\subseteq\mathbb{H}$ containing $\sigma_0$ and real constants $A\ge 0$ and $0\le\vartheta<1$, chosen independently of $n$ and $k$, with the following property: for every natural number $n$ and every integer $k\ge 4$ there is a modular form $P$ of weight $k$ for $\Gamma$ such that, for all $\tau\in\mathbb{H}$,
--   $$P(\tau)=\sum_{\gamma\in\Gamma}\Big(\frac{\gamma\tau-\tau_0}{\gamma\tau-\overline{\tau_0}}\Big)^{n}(\gamma\tau-\overline{\tau_0})^{-k}\,\mathrm{denom}(\gamma,\tau)^{-k},$$
--   where $\gamma\tau$ is the action of $\gamma$ on $\mathbb{H}$, the bar is complex conjugation and $\mathrm{denom}$ is the automorphy factor, and such that for every $\sigma\in U$ the difference between $P(\sigma)$ and the sum of the same terms restricted (by the indicator of the set $\{\gamma\in\Gamma:\gamma\sigma_0=\tau_0\}$) to those $\gamma$ with $\gamma\sigma_0=\tau_0$ has norm at most $A\,\vartheta^{k}\,\big(2\sqrt{\operatorname{Im}\sigma\cdot\operatorname{Im}\tau_0}\big)^{-k}$.
--
--   This is the Petersson construction of Poincaré series attached to the test function $\varphi_{n,k}(w)=\big((w-\tau_0)/(w-\overline{\tau_0})\big)^{n}(w-\overline{\tau_0})^{-k}$ peaked at $\tau_0$, together with a bound showing that near $\sigma_0$ the series is dominated by the finitely many terms with $\gamma\sigma_0=\tau_0$, the remainder decaying geometrically in the weight relative to the invariant gauge $(2\sqrt{\operatorname{Im}\sigma\operatorname{Im}\tau_0})^{-k}$. It is obtained from the general convergence and modularity statement [`ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology), and feeds [`ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology), where forms separating points and providing local parameters are produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_modularForm_peak_sub_le_of_discreteTopology.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.exists_modularForm_peak_sub_le_of_discreteTopology
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (τ₀ σ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ σ₀ ∈ U ∧ ∃ A ϑ : ℝ, 0 ≤ A ∧ 0 ≤ ϑ ∧ ϑ < 1 ∧
      ∀ (n : ℕ) (k : ℤ), 4 ≤ k →
        ∃ P : ModularForm Γ k,
          (∀ τ : ℍ, P τ = ∑' γ : ↥Γ,
            (((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)) ∧
          (∀ σ : ℍ, σ ∈ U →
            ‖P σ - ∑' γ : ↥Γ, Set.indicator {γ : ↥Γ | (γ : GL (Fin 2) ℝ) • σ₀ = τ₀} (fun γ : ↥Γ =>
              (((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (τ₀ : ℂ)) / ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ))) ^ n *
              ((((γ : GL (Fin 2) ℝ) • σ : ℍ) : ℂ) - (starRingEnd ℂ) (τ₀ : ℂ)) ^ (-k) * denom (γ : GL (Fin 2) ℝ) σ ^ (-k)) γ‖
              ≤ A * ϑ ^ k * (2 * Real.sqrt (σ.im * τ₀.im)) ^ (-k)) := by sorry
