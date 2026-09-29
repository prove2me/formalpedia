-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
-- name    : ModularCurve.exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/de0acd05-5f48-557b-b14d-0a19eaf31612
-- title:
--   Edge integrals of a parabolic character are periods
-- statement:
--   Let $N\ge 1$ with the coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$ finite. Let $\gamma_T,\gamma_S$ be functions assigning to each coset $q$ an element of $\Gamma_0(N)$, subject to the hypotheses that, with $\sigma_q$ the chosen representative `Quotient.out q`, one has $\gamma_T(q)=\sigma_{T\cdot q}^{-1}\,T\,\sigma_q$ and $\gamma_S(q)=\sigma_{S\cdot q}^{-1}\,S\,\sigma_q$ in $\mathrm{SL}_2(\mathbb Z)$, for the standard generators $T$ and $S$. Let $\varphi\colon\Gamma_0(N)\to\mathbb Z$ be a group homomorphism (written on the additive copy of $\Gamma_0(N)$) satisfying `IsParabolicHom`, i.e. $\varphi(\gamma)=0$ whenever the integer matrix of $\gamma$ has $\operatorname{tr}(\gamma)^2=4$. The assertion is that there is an element $\Lambda$ of [`ModularCurve.periodLattice N`](def/ModularCurve_PeriodLattice.html#L102), the $\mathbb Z$-span inside the complex dual of $\mathrm{CuspForm}(\Gamma_0(N),2)$ of the period functionals $\gamma\mapsto$ `period N` $\gamma$ attached to integration from $I$ to $\gamma\cdot I$ (so that `period N` $\gamma\,f=F(\gamma\cdot I)-F(I)$ for any equivariant primitive $F$ of $f$), with the following property: for every weight-$2$ cusp form $g$ on $\Gamma_0(N)$ and every family of functions $G_q\colon\mathbb C\to\mathbb C$ with $G_q(z)=g(\sigma_q^{-1}\cdot z)/\operatorname{denom}(\sigma_q^{-1},z)^2$ (the pull-back of $g$ under $\sigma_q^{-1}$, evaluated through `ofComplex`),
--   $$i\sum_q \varphi(\gamma_T(q))\int_{\sqrt3/2}^{\infty}G_q\!\left(-\tfrac12+iy\right)dy\;+\;\tfrac12\sum_q \varphi(\gamma_S(q))\int_{\pi/3}^{2\pi/3}G_q(e^{i\theta})\,i e^{i\theta}\,d\theta\;=\;\Lambda(g).$$
--   The lattice element $\Lambda$ is thus uniform in $g$ and in the choice of the $G_q$.
--
--   This is the integrality half of Poincaré duality on $X_0(N)$ expressed on the cell structure coming from the tiling of the upper half-plane by the translates $\sigma_q^{-1}\mathcal D$ of the standard fundamental domain: an integer parabolic character is read as a cellular $1$-cocycle, and the displayed combination of integrals over the vertical left edge and the unit-circle arc is the period of $g\,dz$ along the dual $1$-chain, which the theorem identifies with an element of the period lattice. It is used by [`ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental`](thm.html#ModularCurve.exists_mem_periodLattice_tendsto_windingPairing_smoothedFundamental) and by [`ModularCurve.petersson_mem_periodLattice_iff_re_period_int`](thm.html#ModularCurve.petersson_mem_periodLattice_iff_re_period_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_mem_periodLattice_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ) :
    ∃ Λ ∈ ModularCurve.periodLattice N,
      ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
        (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          Λ g := by sorry
