-- Prove2me | Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
-- name    : ModularCurve.exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/8a3e4956-410b-53b9-930d-cb48ab7c4562
-- title:
--   Integral parabolic homomorphisms give period-lattice edge-integral functionals
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index with $-1\in\Gamma$ and with finite coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma$, and write $\sigma_q=$ `Quotient.out q` for the chosen representative of a coset $q$. Let $\gamma_T,\gamma_S:\mathrm{SL}_2(\mathbb Z)/\Gamma\to\Gamma$ be families of elements of $\Gamma$ satisfying $\gamma_T(q)=\sigma_{T\cdot q}^{-1}\,T\,\sigma_q$ and $\gamma_S(q)=\sigma_{S\cdot q}^{-1}\,S\,\sigma_q$ for all $q$, where $T,S$ are `ModularGroup.T`, `ModularGroup.S` acting on the quotient by left translation. Let $\varphi:\mathrm{Additive}\,\Gamma\to\mathbb Z$ be an additive homomorphism which is parabolic in the sense of `IsParabolicHom`, i.e. $\varphi(\gamma)=0$ whenever the integer matrix of $\gamma$ has $(\mathrm{tr}\,\gamma)^2=4$. Then there exists a functional $\Lambda$ lying in [`ModularCurve.periodLatticeOf Γ`](def/ModularCurve_PeriodOf.html#L65), the $\mathbb Z$-submodule of $(\mathrm{CuspForm}\,\Gamma\,2)^\vee$ spanned by the functionals `periodOf Γ γ` $=$ `periodAlongOf Γ` attached to the pair of points $i$ and $\gamma\cdot i$ for $\gamma\in\Gamma$, such that for every weight-$2$ cusp form $g$ for $\Gamma$ and every family of functions $G_q:\mathbb C\to\mathbb C$ with $G_q(z)=g(\sigma_q^{-1}\cdot z)/\mathrm{denom}(\sigma_q^{-1},z)^2$ (the argument $z$ being transported to the upper half-plane by `ofComplex`), one has $$i\sum_q \varphi(\gamma_T(q))\int_{\sqrt3/2}^{\infty} G_q\!\left(-\tfrac12+iy\right)dy+\tfrac12\sum_q \varphi(\gamma_S(q))\int_{\pi/3}^{2\pi/3} G_q(e^{i\theta})\,ie^{i\theta}\,d\theta=\Lambda(g).$$ The same $\Lambda$ works for all $g$ and all such families $G$.
--
--   This is the integrality half of Poincaré duality on the modular curve $X_\Gamma$: pairing an integral parabolic homomorphism $\varphi:\Gamma\to\mathbb Z$ against the weight-$2$ cusp forms, by summing edge integrals over the two side-pairing families of the tiling of a fundamental set for $\Gamma$ by translates of the standard fundamental domain, produces a functional in the period lattice. It is used in the construction of the winding pairing over smoothed fundamental domains and in the criterion for a Petersson-type functional to lie in the period lattice in terms of integrality of the real parts of the periods `periodOf`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (SL(2, ℤ) ⧸ Γ)]
    (γT γS : SL(2, ℤ) ⧸ Γ → Γ)
    (hT : ∀ q, ((γT q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (φ : Additive Γ →+ ℤ)
    (hφ : ModularCurve.Period.IsParabolicHom Γ φ) :
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
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
          Λ g := by sorry
