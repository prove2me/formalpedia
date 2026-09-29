-- Prove2me | Theorems.Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
-- name    : ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/f185931f-39f5-5faa-99bc-05ce042e6ed6
-- title:
--   Periods of Γ₀(N) as edge integrals of integral parabolic characters
-- statement:
--   Fix $N \ge 1$ with finitely many cosets in $\mathrm{SL}_2(\mathbb Z)/\Gamma_0(N)$, and let $q \mapsto \mathrm{out}(q)$ denote the canonical choice of representative in $\mathrm{SL}_2(\mathbb Z)$ of a coset $q$. Suppose given maps $\gamma_T, \gamma_S$ from the coset space to $\Gamma_0(N)$ whose underlying matrices are $\gamma_T(q) = \mathrm{out}(T\cdot q)^{-1}\,T\,\mathrm{out}(q)$ and $\gamma_S(q) = \mathrm{out}(S\cdot q)^{-1}\,S\,\mathrm{out}(q)$, with $S,T$ the standard generators and $\cdot$ the left action on the coset space. Then for every $\delta \in \Gamma_0(N)$ there is a homomorphism $\varphi \colon \Gamma_0(N) \to \mathbb Z$ (written additively) which is parabolic in the sense that $\varphi(\gamma) = 0$ whenever $\mathrm{tr}(\gamma)^2 = 4$, and which satisfies the following. For every cusp form $g$ of weight $2$ on $\Gamma_0(N)$ and every family of functions $G_q \colon \mathbb C \to \mathbb C$ indexed by the cosets with $G_q(z) = g(\mathrm{out}(q)^{-1}\cdot z)/\mathrm{denom}(\mathrm{out}(q)^{-1}, z)^2$ for all $z$ (the argument being taken to the upper half-plane via `ofComplex`),
--   $$i \sum_q \varphi(\gamma_T(q)) \int_{\sqrt 3/2}^{\infty} G_q\!\left(-\tfrac12 + iy\right) dy \;+\; \tfrac12 \sum_q \varphi(\gamma_S(q)) \int_{\pi/3}^{2\pi/3} G_q(e^{i\theta})\, i e^{i\theta}\, d\theta \;=\; \mathrm{period}_N(\delta)(g),$$
--   the right-hand side being the value at $g$ of the functional [`ModularCurve.period N δ`](def/ModularCurve_PeriodLattice.html#L92), namely the integral over $t \in [0,1]$ of `periodIntegrand` for the endpoints $i$ and $\delta \cdot i$. The character $\varphi$ depends on $\delta$ only, not on $g$.
--
--   This is the surjectivity half of the Poincaré duality pairing between integral parabolic characters of $\Gamma_0(N)$ and the first homology of $X_0(N)$, realised on the cell structure coming from the tiling of the upper half-plane by the translates $\mathrm{out}(q)^{-1}\mathcal D$ of the standard fundamental domain: the period of $g$ along the geodesic from $i$ to $\delta \cdot i$ is expressed as an integral combination, with multiplicities $\varphi(\gamma_T(q))$ and $\varphi(\gamma_S(q))$, of the integrals of $g\,dz$ over the left vertical edge and the bottom arc of each tile. It is used in the analysis of the period lattice, in [`ModularCurve.petersson_mem_periodLattice_iff_re_period_int`](thm.html#ModularCurve.petersson_mem_periodLattice_iff_re_period_int).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_period
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (δ : CongruenceSubgroup.Gamma0 N) :
    ∃ φ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) φ ∧
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
          ModularCurve.period N δ g := by sorry
