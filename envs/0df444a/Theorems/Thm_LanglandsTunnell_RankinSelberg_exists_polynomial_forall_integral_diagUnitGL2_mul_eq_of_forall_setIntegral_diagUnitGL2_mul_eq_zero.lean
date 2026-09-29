-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
-- name    : LanglandsTunnell.RankinSelberg.exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4b25b102-5a2a-597d-ad71-f0f891dfee6c
-- title:
--   Twisted torus Mellin transform as Laurent polynomial in q^{-s}
-- statement:
--   Let $K$ be a number field and $v$ a maximal ideal of $\mathcal{O}_K$, with completion $F = K_v$ and valuation ring $\mathcal{O}_v$. Let $\varpi \in \mathcal{O}_v$ have nonzero image in $F$ and satisfy $\mathrm{v}(\varpi) = \exp(-1)$, i.e. $\varpi$ is a uniformiser. Let $B : \mathrm{GL}_2(F) \to \mathbb{C}$ be an arbitrary function, $\chi : F^\times \to \mathbb{C}^\times$ an arbitrary group homomorphism (no continuity is assumed), and $h \in \mathrm{GL}_2(F)$; here $F$ carries its Borel $\sigma$-algebra. Write $\mathrm{diag}(x,1)$ for the invertible matrix $\begin{pmatrix} x & 0 \\ 0 & 1\end{pmatrix}$ attached to a unit $x$, and $|a| = \mathrm{modulus}(a)$ for the module of $F$ (the scaling factor of Haar measure under multiplication by $a$, extended by $0$ at $a = 0$). The assertion is: for every Haar measure $\nu$ on $F^\times$, if there is a finite set $T \subseteq \mathbb{Z}$ with $\int_{\{u : \mathrm{v}(u) = 1\}} B(\mathrm{diag}(\varpi^n u,1)\,h)\,\chi(u)\,d\nu(u) = 0$ for all $n \notin T$, then for every $\sigma_0 \in \mathbb{R}$ such that $a \mapsto B(\mathrm{diag}(a,1)h)\chi(a)|a|^{s-1}$ is $\nu$-integrable for every $s$ with $\operatorname{Re} s > \sigma_0$, there exist $P \in \mathbb{C}[X]$ and $m \in \mathbb{Z}$ with $\int_{F^\times} B(\mathrm{diag}(a,1)h)\,\chi(a)\,|a|^{s-1}\,d\nu(a) = q^{ms}\,P(q^{-s})$ for all such $s$, where $q$ is the absolute norm of $v$.
--
--   This is the local rationality mechanism for torus Mellin transforms: vanishing of the $\chi$-twisted averages over the unit shells $\varpi^n \mathcal{O}_v^\times$ outside finitely many $n$ forces the zeta integral along the torus $a \mapsto \mathrm{diag}(a,1)$ to be a Laurent polynomial in $q^{-s}$ on any half-plane of absolute convergence. It is applied with $B$ a $\mathrm{GL}_3$ Whittaker function restricted along $g \mapsto \mathrm{diag}(g,1)$, to show that the local $\mathrm{GL}_3 \times \mathrm{GL}_1$ zeta integrals are Laurent polynomials in $q^{-s}$ at each point of the embedded $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.RankinSelberg.exists_polynomial_forall_integral_diagUnitGL2_mul_eq_of_forall_setIntegral_diagUnitGL2_mul_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    {ϖ : v.adicCompletionIntegers K}
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ))
    (B : GL (Fin 2) (v.adicCompletion K) → ℂ)
    (χ : (v.adicCompletion K)ˣ →* ℂˣ)
    (h : GL (Fin 2) (v.adicCompletion K)) :
    letI := localBorel K v
    ∀ (ν : Measure (v.adicCompletion K)ˣ) [ν.IsHaarMeasure],
      (∃ T : Finset ℤ, ∀ n : ℤ, n ∉ T →
        ∫ u in {u : (v.adicCompletion K)ˣ | Valued.v (u : v.adicCompletion K) = 1},
          B (diagUnitGL2 (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ ^ n * u) *
            h) * ((χ u : ℂˣ) : ℂ) ∂ν = 0) →
      ∀ σ₀ : ℝ,
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun a : (v.adicCompletion K)ˣ =>
            B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1)) ν) →
        ∃ (P : Polynomial ℂ) (m : ℤ), ∀ s : ℂ, σ₀ < s.re →
          ∫ a, B (diagUnitGL2 a * h) * ((χ a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion K) : ℝ) : ℂ) ^ (s - 1) ∂ν =
            (Ideal.absNorm v.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by sorry
