-- Prove2me | Theorems.Thm_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
-- name    : ModularCurve.UVCrossingModel.exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/06958e25-c9ff-5334-80b5-0677f958af79
-- title:
--   Tangent scalars of a branch-preserving automorphism of the crossing model
-- statement:
--   Let $W$ be a complete discrete valuation ring (a commutative domain which is a discrete valuation ring and adically complete for its maximal ideal), let $\varpi \in W$ be irreducible and let $e \ge 1$; write $M = \mathrm{MvPowerSeries}(\mathrm{Fin}\,2, W)/(X_0X_1 - C(\varpi^e))$ for the crossing model `UVCrossingModel W (ϖ ^ e)`, assumed to be a local ring, with its distinguished elements `U` and `V` (the images of the two variables, so $UV = \mathrm{const}(\varpi^e)$) and with $\mathrm{const}(w)$ denoting the image of the constant power series $w \in W$. Let $\theta$ be a ring automorphism of $M$ with $\theta(\mathrm{const}(w)) = \mathrm{const}(w)$ for all $w \in W$ and $\theta(U) \notin (V, \mathrm{const}(\varpi))$. Let $n \ge 1$ be such that the image of $n$ in $W$ is a unit, let $\beta \in M$ be a unit with $\theta^n(V\beta) = V\beta$, and let $c : \mathbb{N} \to W$ be such that for every $k$ with $0 < k < n$ one has $\theta^k(V\beta) - \mathrm{const}(c_k)\,(V\beta) \in \mathfrak{m}_M^2$ and $c_k - 1 \notin \mathfrak{m}_W$. Then there exist $\zeta, \zeta' \in W$ with $\zeta^n = 1$, with $\zeta^k - 1$ a unit for all $0 < k < n$, with $\zeta\zeta' = 1$, with $\theta(U) - \mathrm{const}(\zeta)\,U \in \mathfrak{m}_M^2$ and $\theta(V) - \mathrm{const}(\zeta')\,V \in \mathfrak{m}_M^2$, and such that every $c' \in W$ with $\theta(V\beta) - \mathrm{const}(c')\,(V\beta) \in \mathfrak{m}_M^2$ satisfies $\zeta' - c' \in \mathfrak{m}_W$.
--
--   This linearises, to first order at the crossing point, an automorphism of the local model $W[[U,V]]/(UV - \varpi^e)$ which fixes constants and preserves the two branches: it acts on the two tangent directions by a root of unity $\zeta$ and its inverse, $\zeta$ being primitive in the strong sense that $\zeta^k - 1$ is a unit for $0 < k < n$, and $\zeta'$ is determined modulo $\mathfrak{m}_W$ by any first-order reading of $\theta$ on $V\beta$. It is used in the identification of the completed local rings of modular curves at crossing points of supersingular fibres together with the tangent action of the level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UVCrossingModel_exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem ModularCurve.UVCrossingModel.exists_pow_eq_one_tangent_of_ringEquiv_apply_const_eq_of_iterate_apply_V_mul_eq
    (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    [IsLocalRing (UVCrossingModel W (ϖ ^ e))]
    (θ : UVCrossingModel W (ϖ ^ e) ≃+* UVCrossingModel W (ϖ ^ e))
    (hθc : ∀ w : W, θ (const (ϖ ^ e) w) = const (ϖ ^ e) w)
    (hθU : θ (U (ϖ ^ e)) ∉ Ideal.span {V (ϖ ^ e), const (ϖ ^ e) ϖ})
    (n : ℕ) (hn : 1 ≤ n) (hnW : IsUnit ((n : ℕ) : W))
    (β : UVCrossingModel W (ϖ ^ e)) (hβ : IsUnit β)

    (hfix : (θ ^ n) (V (ϖ ^ e) * β) = V (ϖ ^ e) * β)

    (c : ℕ → W)
    (hread : ∀ k : ℕ, 0 < k → k < n →
      (θ ^ k) (V (ϖ ^ e) * β) - const (ϖ ^ e) (c k) * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2)
    (hfaith : ∀ k : ℕ, 0 < k → k < n → c k - 1 ∉ maximalIdeal W) :
    ∃ ζ ζ' : W, ζ ^ n = 1 ∧ (∀ k : ℕ, 0 < k → k < n → IsUnit (ζ ^ k - 1)) ∧ ζ * ζ' = 1 ∧
      θ (U (ϖ ^ e)) - const (ϖ ^ e) ζ * U (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      θ (V (ϖ ^ e)) - const (ϖ ^ e) ζ' * V (ϖ ^ e) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 ∧
      (∀ c' : W, θ (V (ϖ ^ e) * β) - const (ϖ ^ e) c' * (V (ϖ ^ e) * β) ∈ (maximalIdeal (UVCrossingModel W (ϖ ^ e))) ^ 2 →
        ζ' - c' ∈ maximalIdeal W) := by sorry
