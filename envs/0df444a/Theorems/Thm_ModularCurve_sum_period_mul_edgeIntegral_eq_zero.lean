-- Prove2me | Theorems.Thm_ModularCurve_sum_period_mul_edgeIntegral_eq_zero
-- name    : ModularCurve.sum_period_mul_edgeIntegral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/70e554b1-2f99-505b-b58f-8d4ea9db9ddb
-- title:
--   Bilinear relation between periods and edge integrals on X₀(N)
-- statement:
--   Let $N \ge 1$ be such that $\Gamma_0(N)$ has finitely many cosets in $\mathrm{SL}_2(\mathbb Z)$, and let $k$ and $g$ be cusp forms of weight $2$ for $\Gamma_0(N)$. Let $\gamma_T, \gamma_S$ assign to every coset $q \in \mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ an element of $\Gamma_0(N)$, subject to the requirements that, with $\sigma_q =$ `Quotient.out` $q$ the chosen representative of $q$, the image of $\gamma_T(q)$ in $\mathrm{SL}_2(\mathbb Z)$ is $\sigma_{Tq}^{-1} T \sigma_q$ and that of $\gamma_S(q)$ is $\sigma_{Sq}^{-1} S \sigma_q$, where $T$ and $S$ are the standard generators `ModularGroup.T`, `ModularGroup.S`. Let $G$ assign to every coset $q$ a function $\mathbb C \to \mathbb C$ with $G_q(z) = g(\sigma_q^{-1} \cdot \iota(z)) / \mathrm{denom}(\sigma_q^{-1}, \iota(z))^2$, the weight-$2$ pull-back of $g$ by $\sigma_q^{-1}$, where $\iota =$ `ofComplex` is the retraction of $\mathbb C$ onto $\mathbb H$. Here $\mathrm{period}\,N\,\gamma$ denotes the linear functional on weight-$2$ cusp forms given by `periodAlong` $N$ from $i$ to $\gamma \cdot i$, that is $\int_0^1 \mathrm{periodIntegrand}\,N\,i\,(\gamma\cdot i)\,(\cdot)\,t\,\mathrm dt$. The assertion is
--   $$i \sum_q \mathrm{period}\,N\,(\gamma_T(q))\,(k) \int_{\sqrt3/2}^{\infty} G_q\!\left(-\tfrac12 + iy\right) \mathrm dy \;+\; \tfrac12 \sum_q \mathrm{period}\,N\,(\gamma_S(q))\,(k) \int_{\pi/3}^{2\pi/3} G_q(e^{i\theta})\, i e^{i\theta}\, \mathrm d\theta \;=\; 0,$$
--   both sums being over the cosets $q$.
--
--   This is Riemann's first bilinear relation $\int_{X_0(N)} \omega_k \wedge \omega_g = 0$ for two holomorphic differentials of weight $2$, written out in terms of the periods of $k$ and the integrals of the pull-backs of $g$ over the vertical and circular edges of the standard fundamental domain, tiled by translates $\sigma_q^{-1}\mathcal D$. It is used in the analysis of the period lattice of $X_0(N)$, namely by [`ModularCurve.petersson_mem_periodLattice_iff_re_period_int`](thm.html#ModularCurve.petersson_mem_periodLattice_iff_re_period_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_period_mul_edgeIntegral_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.sum_period_mul_edgeIntegral_eq_zero
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          ModularCurve.period N (γT q) k *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          ModularCurve.period N (γS q) k *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) = 0 := by sorry
