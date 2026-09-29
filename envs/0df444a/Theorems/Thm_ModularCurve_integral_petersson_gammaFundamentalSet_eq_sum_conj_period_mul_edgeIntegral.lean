-- Prove2me | Theorems.Thm_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
-- name    : ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/75d997cd-c69d-52e1-909b-a65510138bee
-- title:
--   Petersson product as a side-pairing sum of periods
-- statement:
--   Fix $N\ge 1$ with $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ finite, and let $k,g$ be cusp forms of weight $2$ for $\Gamma_0(N)$. Let $\gamma_T,\gamma_S$ assign to each coset $q\in \mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ an element of $\Gamma_0(N)$, subject to the hypotheses that $\gamma_T(q)$ equals $\mathrm{out}(T\cdot q)^{-1}\,T\,\mathrm{out}(q)$ and $\gamma_S(q)$ equals $\mathrm{out}(S\cdot q)^{-1}\,S\,\mathrm{out}(q)$ in $\mathrm{SL}_2(\mathbb Z)$, where $\mathrm{out}$ is the chosen representative of a coset and $T,S$ are the standard generators. Let $G$ assign to each $q$ a function on $\mathbb C$ with $G_q(z)=g(\mathrm{out}(q)^{-1}\cdot \mathrm{ofComplex}\,z)/\mathrm{denom}(\mathrm{out}(q)^{-1},\mathrm{ofComplex}\,z)^2$, the weight-$2$ pull-back of $g$ by $\mathrm{out}(q)^{-1}$. Then $i$ times the integral of the weight-$2$ Petersson integrand `UpperHalfPlane.petersson 2 k g` over the fundamental set $\bigcup_q \mathrm{out}(q)^{-1}\cdot\mathcal D$ ($\mathcal D$ the standard fundamental domain of $\mathrm{SL}_2(\mathbb Z)$) equals $$\tfrac i2\sum_q \overline{P_k(\gamma_T(q))}\int_{\sqrt3/2}^{\infty} G_q(-\tfrac12+iy)\,dy \;+\;\tfrac14\sum_q \overline{P_k(\gamma_S(q))}\int_{\pi/3}^{2\pi/3} G_q(e^{i\theta})\,i e^{i\theta}\,d\theta,$$ where $P_k(\gamma)=\mathrm{period}\,N\,\gamma$ applied to $k$ is the integral of the period integrand along the path from $i$ to $\gamma\cdot i$, parametrised over $t\in[0,1]$.
--
--   This is the Riemann bilinear relation for $X_0(N)$, written concretely for the tiling of the standard fundamental set of $\Gamma_0(N)$ by translates of $\mathcal D$: the left-hand side is $i$ times the unnormalised Petersson product of $k$ and $g$, while the right-hand side involves only periods of $k$ along the side-pairing elements attached to $T$ and $S$ and integrals of the pulled-back $g$ along the left vertical edge and the bottom arc of each tile. It is used by [`ModularCurve.petersson_mem_periodLattice_iff_re_period_int`](thm.html#ModularCurve.petersson_mem_periodLattice_iff_re_period_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups ComplexConjugate

theorem ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
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
    Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N),
        UpperHalfPlane.petersson 2 k g τ) =
      Complex.I / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γT q) k) *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 4 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γS q) k) *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) := by sorry
