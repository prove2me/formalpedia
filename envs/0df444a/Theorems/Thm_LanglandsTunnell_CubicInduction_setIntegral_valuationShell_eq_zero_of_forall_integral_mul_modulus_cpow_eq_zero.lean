-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
-- name    : LanglandsTunnell.CubicInduction.setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/b76365cc-4a23-53bc-8855-cefe1c1225f3
-- title:
--   Vanishing Mellin transform forces vanishing shell integrals
-- statement:
--   Let $v$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_v$ for the $v$-adic completion, equipped with its Borel $\sigma$-algebra, and let $F:\mathbb{Q}_v^{\times}\to\mathbb{C}$ be a function, $\sigma$ a real number and $K$ an integer. The measure used throughout on $\mathbb{Q}_v^{\times}$ is the pullback along $a\mapsto a$ of the multiplicative measure attached to the self-dual Haar measure, i.e. of the measure obtained from the additive Haar measure normalised on $\mathcal{O}_v$ and scaled by $(\mathrm{N}v)^{-\ell/2}$, $\ell$ the level of the local standard additive character, by restricting to $\mathbb{Q}_v\setminus\{0\}$ and multiplying by the density $x\mapsto \mathrm{mod}(x)^{-1}$, where $\mathrm{mod}$ is the module (the distributive Haar character). Assume: (i) $F(a)=0$ whenever $\mathrm{v}(a)>\exp K$, so $F$ is supported in the region $\mathrm{v}(a)\le\exp K$; (ii) for every $s\in\mathbb{C}$ with $\mathrm{Re}\,s>\sigma$ the function $a\mapsto F(a)\,\mathrm{mod}(a)^{s-1}$ is integrable for that measure; (iii) its integral over $\mathbb{Q}_v^{\times}$ vanishes for all such $s$. The conclusion is that for every integer $k$ the integral of $F$ over the shell $\{a:\mathrm{v}(a)=\exp(-k)\}$ vanishes.
--
--   This is the uniqueness-of-coefficients step for the shell (Laurent) expansion of a local Mellin, or Tate-type, integral: a function supported in a half-range of valuations whose Mellin transform vanishes on a right half-plane has all its shell averages equal to zero. It is used in establishing convergence and non-vanishing of the local $GL_3\times GL_1$ zeta integrals appearing in the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.setIntegral_valuationShell_eq_zero_of_forall_integral_mul_modulus_cpow_eq_zero
    (v : HeightOneSpectrum (𝓞 ℚ)) (F : (v.adicCompletion ℚ)ˣ → ℂ) (σ : ℝ) (K : ℤ)
    (hsupp : ∀ a : (v.adicCompletion ℚ)ˣ, WithZero.exp K < Valued.v (a : v.adicCompletion ℚ) → F a = 0)
    (hint : letI := localBorel ℚ v
      ∀ s : ℂ, σ < s.re → Integrable
        (fun a : (v.adicCompletion ℚ)ˣ => F a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1))
        (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))))
    (hzero : letI := localBorel ℚ v
      ∀ s : ℂ, σ < s.re →
        ∫ a : (v.adicCompletion ℚ)ˣ, F a * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0) :
    letI := localBorel ℚ v
    ∀ k : ℤ, ∫ a in {a : (v.adicCompletion ℚ)ˣ | Valued.v (a : v.adicCompletion ℚ) = WithZero.exp (-k)}, F a
      ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ v))) = 0 := by sorry
