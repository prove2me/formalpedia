-- Prove2me | Theorems.Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf
-- name    : ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/ceb7f673-28bb-51d7-9581-829659959636
-- title:
--   Manin: every period via an integer parabolic homomorphism
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index with $-1\in\Gamma$ and with finitely many cosets in $\mathrm{SL}_2(\mathbb Z)/\Gamma$, and write $\sigma_q$ for the chosen representative `Quotient.out q` of a coset $q$. Suppose given two families $\gamma_T,\gamma_S$ of elements of $\Gamma$ indexed by the cosets, satisfying, in $\mathrm{SL}_2(\mathbb Z)$, $\gamma_T(q)=\sigma_{T\cdot q}^{-1}\,T\,\sigma_q$ and $\gamma_S(q)=\sigma_{S\cdot q}^{-1}\,S\,\sigma_q$ for all $q$, where $T,S$ are the standard generators `ModularGroup.T`, `ModularGroup.S`, and let $\delta\in\Gamma$. Then there exists a group homomorphism $\varphi$ from $\Gamma$ (written additively) to $\mathbb Z$ such that $\varphi$ satisfies `IsParabolicHom`, i.e. $\varphi(\gamma)=0$ for every $\gamma\in\Gamma$ whose integral matrix has trace with square $4$, and such that for every weight-$2$ cusp form $g$ for $\Gamma$ and every family $G_q:\mathbb C\to\mathbb C$ of functions with $G_q(z)=g(\sigma_q^{-1}\cdot z)/\mathrm{denom}(\sigma_q^{-1},z)^2$ (evaluation through `UpperHalfPlane.ofComplex`) one has $$i\sum_q \varphi(\gamma_T(q))\int_{\sqrt3/2}^{\infty}G_q\!\left(-\tfrac12+iy\right)dy+\tfrac12\sum_q \varphi(\gamma_S(q))\int_{\pi/3}^{2\pi/3}G_q(e^{i\theta})\,i e^{i\theta}\,d\theta=\mathrm{periodOf}\,\Gamma\,\delta\,g,$$ the right-hand side being the period of $g$ along the path from $i$ to $\delta\cdot i$, defined as $\int_0^1$ of the period integrand for the pair $(i,\delta\cdot i)$. The first sum is a Bochner integral over $(\sqrt3/2,\infty)$, the second an interval integral.
--
--   This is the surjectivity half of Poincaré duality on the modular curve $X_\Gamma$ in Manin's form: every period of a weight-$2$ cusp form along an element of $\Gamma$ is realised as the pairing of that form against the $1$-chain dual to the cellular cocycle attached to an integer-valued homomorphism vanishing on elements of trace $\pm2$, the edges of the tiling being the vertical line through $-1/2$ and the unit-circle arc from $e^{i\pi/3}$ to $e^{2i\pi/3}$. It is used in the proof of [`ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int`](thm.html#ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int), which identifies the period lattice inside the dual of the space of weight-$2$ cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (SL(2, ℤ) ⧸ Γ)]
    (γT γS : SL(2, ℤ) ⧸ Γ → Γ)
    (hT : ∀ q, ((γT q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (δ : Γ) :
    ∃ φ : Additive Γ →+ ℤ,
      ModularCurve.Period.IsParabolicHom Γ φ ∧
      ∀ (g : CuspForm Γ 2)
        (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ),
        (∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
          denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) →
        Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
              ((φ (Additive.ofMul (γT q)) : ℤ) : ℂ) *
                (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
            1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
              ((φ (Additive.ofMul (γS q)) : ℤ) : ℂ) *
                (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                  G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) =
          ModularCurve.periodOf Γ δ g := by sorry
