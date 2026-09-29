-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
-- name    : LanglandsTunnell.RankinSelberg.forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/31abcea4-f173-5b79-8e9e-1a7d23d1aad3
-- title:
--   Pull-down of a local det-zeta integral identity
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, and equip $GL_2$ of the completion $\mathbb{Q}_p$ at $p$ with its Borel $\sigma$-algebra (`localGLBorel`, registered as a Borel space). The assertion is: for every measure $\mu_2$ on $GL_2(\mathbb{Q}_p)$, every function $f\colon GL_2(\mathbb{Q}_p)\to\mathbb{C}$, every $\tau\in\mathbb{C}$ and every $B\in\mathbb{Z}$ such that $v(\det g)\le \mathrm{exp}(B)$ in the value group with zero whenever $f(g)\neq 0$ (a bound on the determinant valuation over the support of $f$), and for all reals $\sigma_u,\sigma_2$ and every $a\colon\mathbb{Z}\to\mathbb{C}$ with finite support, if (i) for all $s$ with $\operatorname{Re} s>\sigma_u$ the function $g\mapsto f(g)\,\mathrm{modulus}(\det g)^{s+\tau}$ is $\mu_2$-integrable, where $\mathrm{modulus}(x)$ is $0$ for $x=0$ and otherwise the distributive Haar character of the scaling by $x$, and (ii) for all $s$ with $\operatorname{Re} s>\sigma_2$ that integral equals the finite sum $\sum_{i\in\mathbb{Z}} N^{-is}a_i$ with $N=\mathrm{absNorm}(p)$, then (ii) already holds on the larger half-plane: for all $s$ with $\operatorname{Re} s>\sigma_u$, $\int f(g)\,\mathrm{modulus}(\det g)^{s+\tau}\,d\mu_2(g)=\sum_{i\in\mathbb{Z}} N^{-is}a_i$.
--
--   This is the pull-down step in the local theory of Rankin–Selberg and Tate zeta integrals: an identity between a determinant-twisted local integral and a finite exponential sum in $N^{-s}$, valid a priori only far to the right, is propagated to the whole half-plane of absolute convergence, by uniqueness of the coefficients of a generalised Dirichlet series in $N^{-s}$. It feeds the construction of the Laurent functional equation for local integrals attached to principal series in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal

theorem LanglandsTunnell.RankinSelberg.forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (τ : ℂ) (B : ℤ),
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), f g ≠ 0 →
        Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≤ WithZero.exp B) →
      ∀ (σu σ₂ : ℝ) (a : ℤ → ℂ), (Function.support a).Finite →
        (∀ s : ℂ, σu < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ)) μ₂) →
        (∀ s : ℂ, σ₂ < s.re →
          ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i) →
        ∀ s : ℂ, σu < s.re →
          ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i := by sorry
