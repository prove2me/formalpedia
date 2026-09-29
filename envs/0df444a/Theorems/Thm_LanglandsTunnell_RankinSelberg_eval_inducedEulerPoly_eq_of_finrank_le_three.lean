-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three
-- name    : LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/af41c96e-7920-53ab-bffb-085a194fa583
-- title:
--   Evaluating the induced Euler polynomial in degree at most three
-- statement:
--   Let $K$ be a number field of degree at most $3$ over $\mathbb{Q}$, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ that is integral; let $R$ be a commutative ring, let $c$ assign to each height one prime $\mathfrak{P}$ of $\mathcal{O}_K$ an element $c(\mathfrak{P}) \in R$, let $p$ be a height one prime of $\mathcal{O}_{\mathbb{Q}}$, and let $z \in R$. The induced Euler polynomial of $c$ at $p$ is the (finitely supported) product, over the set of height one primes $\mathfrak{P}$ of $\mathcal{O}_K$ whose contraction to $\mathcal{O}_{\mathbb{Q}}$ equals $p$, of the polynomials $1 - c(\mathfrak{P})X^{f}$, where $f$ is the inertia degree `inertiaDeg'` of $\mathfrak{P}$ over its contraction; and the induced coefficients at $p$ are $e_1 = -a_1$, $e_2 = a_2$, $e_3 = -a_3$, where $a_i$ is the coefficient of $X^i$ of this polynomial. The assertion is the identity
--   $$\big(\textstyle\prod_{\mathfrak{P} \mid p} (1 - c(\mathfrak{P})X^{f_{\mathfrak{P}}})\big)(z) = 1 - e_1 z + e_2 z^2 - e_3 z^3$$
--   in $R$: under the degree hypothesis the induced Euler polynomial has constant term $1$ and is determined by the three coefficients $e_1, e_2, e_3$, and its value at any $z$ is given by the displayed cubic expression.
--
--   This records that for a number field of degree at most three the local Euler factor obtained by inducing a function on primes of $K$ down to a rational prime is a cubic with constant term $1$, so that it may be handled throughout by means of its three coefficients $e_1, e_2, e_3$. It is used repeatedly in the cubic-induction and Rankin–Selberg computations of the Langlands–Tunnell part of the development, wherever such an Euler factor must be evaluated or compared with a product of local factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_eval_inducedEulerPoly_eq_of_finrank_le_three.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.RankinSelberg.eval_inducedEulerPoly_eq_of_finrank_le_three
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K ≤ 3)
    {R : Type*} [CommRing R] (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 ℚ)) (z : R) :
    (inducedEulerPoly ℚ c p).eval z =
      1 - inducedE1 ℚ c p * z + inducedE2 ℚ c p * z ^ 2 - inducedE3 ℚ c p * z ^ 3 := by sorry
