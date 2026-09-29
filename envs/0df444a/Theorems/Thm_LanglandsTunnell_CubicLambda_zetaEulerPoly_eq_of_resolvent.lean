-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent
-- name    : LanglandsTunnell.CubicLambda.zetaEulerPoly_eq_of_resolvent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d6e75d02-8320-503f-957b-0f8165e52c55
-- title:
--   Euler factor of ζ_K for a non-normal cubic field
-- statement:
--   Let $K$, $L$, $E$ be number fields whose rings of integers carry compatible integral algebra structures: $\mathcal O_K$, $\mathcal O_L$, $\mathcal O_E$ are integral $\mathcal O_{\mathbb Q}$-algebras, and $\mathcal O_E$ is moreover an integral algebra over both $\mathcal O_L$ and $\mathcal O_K$, compatibly with $\mathcal O_{\mathbb Q}$; assume $E/\mathbb Q$ is Galois, $[K:\mathbb Q]=3$ with $K$ not normal over $\mathbb Q$, $[L:\mathbb Q]=2$ and $[E:\mathbb Q]=6$. Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$ and $c$ a complex-valued function on the height-one primes of $\mathcal O_L$ such that: (H1) for every prime $\mathfrak q$ of $L$ lying under $p$ and every prime $\mathfrak Q$ of $E$ lying over $\mathfrak q$, $c(\mathfrak q)$ is a primitive root of unity of order the inertia degree of $\mathfrak Q$ over $\mathfrak q$; (H3) any two distinct primes $\mathfrak q\neq\mathfrak q'$ of $L$ above $p$ satisfy $c(\mathfrak q')=c(\mathfrak q)^{-1}$; and every prime $\mathfrak P$ of $E$ above $p$ has ramification index $1$ over $p$. Then $$\prod_{\mathfrak P\mid p,\ \mathfrak P\subset\mathcal O_K}\bigl(1-X^{f(\mathfrak P/p)}\bigr)=(1-X)\prod_{\mathfrak q\mid p,\ \mathfrak q\subset\mathcal O_L}\bigl(1-c(\mathfrak q)X^{f(\mathfrak q/p)}\bigr)$$ as polynomials over $\mathbb C$, the products being the finite products over the fibres of $p$ and $f$ denoting inertia degree over $p$.
--
--   This is the local, Euler-factor form of the classical factorisation $\zeta_K=\zeta\cdot L(\theta)$ for a non-normal cubic field $K$ with quadratic resolvent $L$ and Galois closure $E$, at primes unramified in $E$, obtained from the possible splitting types of $p$ in a degree-six $S_3$-extension. It feeds the construction of the induced automorphic data in the cubic-induction step of the Langlands–Tunnell argument, being cited by the two statements [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three) and [`LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound`](thm.html#LanglandsTunnell.CubicInduction.exists_isAdmissibleTwist_eulerCoeff_eq_inducedE3_of_finrank_eq_three_conductorBound).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicLambda_zetaEulerPoly_eq_of_resolvent.lean

import Definitions.Def_LanglandsTunnell_CubicLambda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.CubicLambda.zetaEulerPoly_eq_of_resolvent
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (L : Type) [Field L] [NumberField L] [Algebra (𝓞 ℚ) (𝓞 L)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 L)]
    (E : Type) [Field E] [NumberField E]
    [Algebra (𝓞 ℚ) (𝓞 E)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 E)]
    [Algebra (𝓞 L) (𝓞 E)] [Algebra.IsIntegral (𝓞 L) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 L) (𝓞 E)]
    [Algebra (𝓞 K) (𝓞 E)] [Algebra.IsIntegral (𝓞 K) (𝓞 E)] [IsScalarTower (𝓞 ℚ) (𝓞 K) (𝓞 E)]
    [IsGalois ℚ E]
    (hK : Module.finrank ℚ K = 3) (hKn : ¬ Normal ℚ K)
    (hL : Module.finrank ℚ L = 2) (hE : Module.finrank ℚ E = 6)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : HeightOneSpectrum (𝓞 L) → ℂ)
    (H1 : ∀ (𝔮 : HeightOneSpectrum (𝓞 L)) (𝔔 : HeightOneSpectrum (𝓞 E)), 𝔮.under (𝓞 ℚ) = p →
      𝔔.under (𝓞 L) = 𝔮 → IsPrimitiveRoot (c 𝔮) (𝔮.asIdeal.inertiaDeg' 𝔔.asIdeal))
    (H3 : ∀ 𝔮 𝔮' : HeightOneSpectrum (𝓞 L), 𝔮.under (𝓞 ℚ) = p → 𝔮'.under (𝓞 ℚ) = p → 𝔮 ≠ 𝔮' →
      c 𝔮' = (c 𝔮)⁻¹)
    (hp : ∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 ℚ) = p →
      p.asIdeal.ramificationIdx' 𝔓.asIdeal = 1) :
    zetaEulerPoly K p = (Polynomial.C 1 - Polynomial.X) * inducedEulerPoly ℚ c p := by sorry
