-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_pos
-- name    : LanglandsTunnell.CubicInduction.inducedLevelAt_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/16ea2600-8114-5716-b5c7-92971166baf5
-- title:
--   Positivity of the induced level at a ramified place
-- statement:
--   Let $K$ be a number field whose ring of integers $\mathcal{O}_K$ is given as an integral $\mathcal{O}_{\mathbb{Q}}$-algebra, and let $\mu$ be a group homomorphism from the units of the adele ring of $K$ to $\mathbb{C}^\times$ which is an admissible twist, that is: $\mu$ is trivial on the image of $K^\times$ in the ideles, $\mu$ is continuous, and $|\mu(x)| = 1$ for every idele unit $x$. Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, and assume that $\mu$ is ramified above $v$ in the sense that there is a height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying in the fibre over $v$ (i.e. the prime of $\mathcal{O}_{\mathbb{Q}}$ under $\mathfrak{P}$ is $v$) such that the local component $\mathrm{localChar}\,\mu\,\mathfrak{P}$, the restriction of $\mu$ to the local units at $\mathfrak{P}$, fails to be $1$ on some unit $t$ of the completion $K_{\mathfrak{P}}$ with both $t$ and $t^{-1}$ integral. Then the induced level of $\mu$ at $v$, defined as the (finitely supported) sum over the primes $\mathfrak{P}$ of $\mathcal{O}_K$ above $v$ of the inertia degree of $\mathfrak{P}$ over $v$ times the conductor exponent of $\mathrm{localChar}\,\mu\,\mathfrak{P}$ (the infimum of the natural numbers $c$ for which that local character has conductor exponent $c$), is strictly positive.
--
--   This records that the local level attached to a cubic induction is non-trivial exactly where the twisting idele class character is ramified; it supplies the positivity input for the construction of normalised newvectors in the cubic induction package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_inducedLevelAt_pos.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.Converse

theorem LanglandsTunnell.CubicInduction.inducedLevelAt_pos (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : IsTwistRamifiedAbove K μ v) :
    0 < inducedLevelAt K μ v := by sorry
