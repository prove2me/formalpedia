-- Prove2me | Theorems.Thm_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant
-- name    : ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/8697798b-0a6c-5d34-8d44-8c488094cc1d
-- title:
--   Bounded denominators for rational q-expansions of level N
-- statement:
--   Let $N$ be a positive integer, $m$ a natural number, and let $G\colon \mathfrak H \to \mathbb C$ be a function on the upper half-plane that is holomorphic in the sense of being `MDifferentiable` for the standard complex-manifold charts on $\mathfrak H$ and on $\mathbb C$. Assume: (i) $G$ is invariant under the principal congruence subgroup, i.e. $G(\gamma \cdot \tau) = G(\tau)$ for every $\gamma$ in `CongruenceSubgroup.Gamma N` and every $\tau \in \mathfrak H$; (ii) for every $\alpha \in \mathrm{SL}_2(\mathbb Z)$ the product of $\tau \mapsto G(\alpha \cdot \tau)$ with the $m$-th power of the discriminant cusp form `ModularForm.discriminant` is bounded as $\operatorname{Im}\tau \to \infty$ (`UpperHalfPlane.IsBoundedAtImInfty`); and (iii) every coefficient of the level-$N$ $q$-expansion `UpperHalfPlane.qExpansion N` of $G \cdot \Delta^m$, i.e. the expansion in $q_N = e^{2\pi i \tau / N}$, is the image in $\mathbb C$ of a rational number. The conclusion is that these coefficients have bounded denominators: there exists a nonzero integer $D$ such that for every $n \in \mathbb N$ the product of $D$ with the $n$-th coefficient of the $q$-expansion of $G \cdot \Delta^m$ is the image in $\mathbb C$ of some integer.
--
--   This is the bounded-denominator assertion of the classical theory of the modular function field of level $N$ (the relevant clause of Shimura's Theorem 3.52), here in the form applying to weight-zero quotients $G = F/\Delta^m$ for $\Gamma(N)$. It feeds [`ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion`](thm.html#ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion), where a rational $q$-expansion is rescaled to an integral one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups Manifold in

theorem ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant
    (N : ℕ) [NeZero N] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : UpperHalfPlane, G (γ • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ)) :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ n : ℕ, ∃ z : ℤ,
      (D : ℂ) * (UpperHalfPlane.qExpansion N (G * ModularForm.discriminant ^ m)).coeff n = (z : ℂ) := by sorry
