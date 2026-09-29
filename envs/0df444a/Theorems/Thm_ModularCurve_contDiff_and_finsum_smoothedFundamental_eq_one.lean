-- Prove2me | Theorems.Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one
-- name    : ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/64282855-ecd9-5ce1-9d96-c8c7a0b92dfa
-- title:
--   Smoothed fundamental function: smoothness and partition-of-unity properties
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}(2,\mathbb Z)$ of finite index and let $T$ be a real number, and write $h =$ [`ModularCurve.smoothedFundamental Γ T`](def/ModularCurve_SmoothedFundamental.html#L170) for the function $\mathbb C \to \mathbb R$ sending $z$ to the (unordered) sum $\sum_{q \in \mathrm{SL}(2,\mathbb Z)/\Gamma} \mathrm{puCut}_T(\mathrm{mob}(\sigma_q, z))$, where $\sigma_q$ is the chosen representative `Quotient.out q` of the coset $q$, $\mathrm{mob}(\gamma, z) = \mathrm{num}\,\gamma\, z / \mathrm{denom}\,\gamma\, z$ is the Möbius expression attached to $\gamma$, and $\mathrm{puCut}_T$ is the pointwise product of the two auxiliary real functions `pu T` and `gcut T`. The theorem asserts the conjunction of eight statements: $h$ is of class $C^n$ over $\mathbb R$ for every $n \in \mathbb N^\infty$; $h$ has compact support; the topological support of $h$ is contained in the open upper half plane $\{z : 0 < \operatorname{Im} z\}$; $h \ge 0$ everywhere; for every $\tau \in \mathbb H$ the set of $\gamma \in \Gamma$ with $h(\gamma \cdot \tau) \ne 0$ is finite; for every such $\tau$ one has $\sum_{\gamma \in \Gamma} h(\gamma \cdot \tau) \le 1$; this sum equals $1$ whenever $\max(\operatorname{Im} \tau, (\operatorname{Im} \tau)^{-1}) \le T$; and there is a finite subset $G \subseteq \mathrm{SL}(2,\mathbb Z)$ such that for every $\delta \notin G$ and every $\tau \in \mathbb H$ with $h(\tau) \ne 0$ one has $h(\delta \cdot \tau) = 0$. The sums over $\Gamma$ range over group elements, so $\gamma$ and $-\gamma$ contribute separately.
--
--   This packages the smoothed fundamental function of $\Gamma$, truncated at height $T$, as a smooth compactly supported automorphic partition of unity on the upper half plane away from the cusps, the analytic substitute for a fundamental polygon in unfolding arguments. It is used in the integration-by-unfolding and Stokes-type results on $\Gamma \backslash \mathbb H$, including the convergence statements for integrals against the smoothed fundamental function and the local-model computations of $\bar\partial$-logarithmic-derivative integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups Topology ContDiff

theorem ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (T : ℝ) :
    (∀ n : ℕ∞, ContDiff ℝ n (ModularCurve.smoothedFundamental Γ T)) ∧
    HasCompactSupport (ModularCurve.smoothedFundamental Γ T) ∧
    tsupport (ModularCurve.smoothedFundamental Γ T) ⊆ {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 ≤ ModularCurve.smoothedFundamental Γ T z) ∧
    (∀ τ : ℍ, (Function.support fun γ : Γ =>
        ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ)).Finite) ∧
    (∀ τ : ℍ,
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) ≤ 1) ∧
    (∀ τ : ℍ, max τ.im τ.im⁻¹ ≤ T →
      ∑ᶠ γ : Γ, ModularCurve.smoothedFundamental Γ T (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = 1) ∧
    (∃ G : Finset SL(2, ℤ), ∀ δ : SL(2, ℤ), δ ∉ G → ∀ τ : ℍ,
      ModularCurve.smoothedFundamental Γ T τ ≠ 0 →
        ModularCurve.smoothedFundamental Γ T ((δ • τ : ℍ) : ℂ) = 0) := by sorry
