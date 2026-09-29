-- Prove2me | Theorems.Thm_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
-- name    : ModularCurve.integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/257a22b0-b7a9-53ae-abdf-99f74e86c551
-- title:
--   Stokes with side pairing on a Γ-fundamental set
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index (the quotient $\mathrm{SL}_2(\mathbb Z)/\Gamma$ being finite) with $-1\in\Gamma$. Let $L:\mathbb C\to\mathbb C$ and $L':\mathbb C\to(\mathbb C\to_{L[\mathbb R]}\mathbb C)$ be such that $L$ has Fréchet derivative $L'z$ at every $z$ with $\operatorname{Im}z>0$ and $L'$ is continuous on $\{\operatorname{Im}z>0\}$; let $c:\mathrm{SL}_2(\mathbb Z)\to\mathbb C$ satisfy $L(\gamma\tau)=L(\tau)+c(\gamma)$ for all $\gamma\in\Gamma$ and $\tau\in\mathbb H$; and assume that for each $\sigma\in\mathrm{SL}_2(\mathbb Z)$ there are constants $C,Y$ with $\|L(\sigma\cdot\mathrm{ofComplex}\,z)\|\le C$ and $\|\mathrm{fderiv}_{\mathbb R}(u\mapsto L(\sigma\cdot\mathrm{ofComplex}\,u))(z)\|\le C$ whenever $\operatorname{Im}z\ge Y$, where `ofComplex` is the retraction of $\mathbb C$ onto $\mathbb H$. Let $g$ be a cusp form of weight $2$ for $\Gamma$, and let $G:\mathrm{SL}_2(\mathbb Z)/\Gamma\to\mathbb C\to\mathbb C$ be given by $G_q(z)=g(\sigma_q^{-1}\cdot\mathrm{ofComplex}\,z)/\mathrm{denom}(\sigma_q^{-1},\mathrm{ofComplex}\,z)^2$, with $\sigma_q=\mathtt{Quotient.out}\,q$ the chosen coset representatives. Then the function $\tau\mapsto\tfrac12\bigl(L'\tau(1)+i\,L'\tau(i)\bigr)\,g(\tau)\,(\operatorname{Im}\tau)^2$ is integrable on the fundamental set $\bigcup_q\sigma_q^{-1}\mathcal D$ ($\mathcal D$ the standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}_2(\mathbb Z)$, integration with respect to the invariant measure of $\mathbb H$, whose density $y^{-2}$ the factor $(\operatorname{Im}\tau)^2$ compensates), and its integral over that set equals $$\frac{1}{2i}\Bigl(i\sum_q c\bigl(\sigma_{Tq}^{-1}T\sigma_q\bigr)\int_{\sqrt3/2}^{\infty}G_q\bigl(-\tfrac12+iy\bigr)\,dy+\tfrac12\sum_q c\bigl(\sigma_{Sq}^{-1}S\sigma_q\bigr)\int_{\pi/3}^{2\pi/3}G_q(e^{i\theta})\,ie^{i\theta}\,d\theta\Bigr),$$ the sums running over $q\in\mathrm{SL}_2(\mathbb Z)/\Gamma$ and $S,T$ being the standard generators.
--
--   This is Stokes' (Green's) theorem applied on the cut fundamental polygon of $\Gamma$: the $\bar\partial$-derivative of a $\Gamma$-quasi-periodic function against a weight-two cusp form is expressed through the side-pairing constants $c(\sigma_{Tq}^{-1}T\sigma_q)$, $c(\sigma_{Sq}^{-1}S\sigma_q)$ and the vertical and circular edge integrals of the pulled-back differential $g\,dz$. It feeds the period-lattice statements [`ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental`](thm.html#ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental) and [`ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental`](thm.html#ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
    (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
    (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
    (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
    (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)
    (g : CuspForm Γ 2) (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    IntegrableOn (fun τ : ℍ => (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2))
      (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) ∧
    (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2)) =
      1 / (2 * Complex.I) *
        (Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
          1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
              (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))) := by sorry
