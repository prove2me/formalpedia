-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous
-- name    : LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/b296a4e4-7ce1-51e7-a6bf-6f6198a29574
-- title:
--   Finitely many bad places for a continuous idele character
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ which is integral, and let $\mu \colon (\mathbb{A}_K)^{\times} \to \mathbb{C}^{\times}$ be a homomorphism of monoids from the unit group of the adele ring of $K$ to $\mathbb{C}^{\times}$ which is continuous. The assertion is that the set of those $v$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$ for which `IsBadPlace K μ v` holds is finite. By definition, $v$ is such a place precisely when at least one of the following two conditions holds: either there is a height-one prime $\mathfrak{P}$ of $\mathcal{O}_K$ lying in the fibre `primeFibre ℚ K v` over $v$ (that is, with contraction $\mathfrak{P} \cap \mathcal{O}_{\mathbb{Q}} = v$) whose ramification index `Ideal.ramificationIdx'` over $v$ is different from $1$; or there is such a prime $\mathfrak{P}$ in the fibre at which the predicate `IsUnramifiedCharAt` fails for $\mu$, i.e. at which $\mu$ is ramified. So: only finitely many rational primes either ramify in $K$ or carry a prime of $K$ above them at which $\mu$ ramifies.
--
--   This is the standard finiteness statement guaranteeing that an idele class character of a number field, together with the extension $K/\mathbb{Q}$, has only finitely many bad rational primes, so that Euler products and level structures attached to the cubic-induction Hecke datum differ from their unramified shape at only finitely many places. It is used throughout the construction of the induced automorphic data, for instance by the results on entirety of induced Euler twists and on the local zeta factors of the cubic induction form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_finite_setOf_isBadPlace_of_continuous.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.finite_setOf_isBadPlace_of_continuous
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : Continuous μ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | IsBadPlace K μ v}.Finite := by sorry
