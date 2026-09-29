-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
-- name    : LanglandsTunnell.RankinSelberg.differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/817e52c5-97ed-530d-b1db-4e08769cd213
-- title:
--   Holomorphy of Rankin–Selberg L-functions beyond the abscissa
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, equipped with an integral algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$, let $\Pi$ be a complex Hecke eigensystem for $\mathbb{Q}$ (a non-zero level ideal together with functions $p \mapsto \Pi.a\,p$ and $p\mapsto \Pi.b\,p$ on the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$), let $\mu$ be a homomorphism from the idele units of $K$ to $\mathbb{C}^\times$, let $SQ$ be a finite set of primes of $\mathbb{Q}$, and let $\Gamma_{\mathbb{R}},\Gamma_{\mathbb{C}},\Gamma_{\mathbb{R}}^{\vee},\Gamma_{\mathbb{C}}^{\vee}$ be arbitrary multisets of complex numbers. Assume: $\|\mu(\text{uniformizerIdele}\,K\,\mathfrak{P})\| = 1$ for every prime $\mathfrak{P}$ of $\mathcal{O}_K$ at which $\mu$ is unramified, in the sense that the induced local character on $(\mathfrak{P}\text{-adic completion})^\times$ is trivial on units of the valuation ring; $\|\Pi.b\,p\| = 1$ for $p \notin SQ$; $\sum_p \|\Pi.a\,p\|\, N(p)^{-\sigma}$ converges for every real $\sigma > 1$, where $N(p)$ is the absolute norm of $p$; and for each $p \notin SQ$ there exist $\gamma,\delta \in \mathbb{C}$ with $\gamma+\delta = \Pi.a\,p$, $\gamma\delta = \Pi.b\,p$ and $\|\gamma\|,\|\delta\| < \sqrt{N(p)}$. Form the $L$-datum `rsDatum` indexed by the primes $p \notin SQ$, with $\mathrm{norm}(p)=N(p)$, Euler factor the degree-$6$ polynomial $\text{rsEulerPoly}(\Pi.a\,p, \Pi.b\,p, e_1, e_2, e_3)$, where $e_1, e_2, e_3$ are, up to sign, the coefficients in degrees $1,2,3$ of `inducedEulerPoly` at $p$ of the function sending a prime $\mathfrak{P}$ of $\mathcal{O}_K$ to $\mu(\text{uniformizerIdele}\,K\,\mathfrak{P})$ if $\mu$ is unramified at $\mathfrak{P}$ and to $0$ otherwise, dual Euler factor the same polynomial in $(\Pi.a\,p/\Pi.b\,p, (\Pi.b\,p)^{-1})$ and the corresponding induced coefficients of the pointwise inverse function, archimedean data the four given multisets, abscissa $1$, centre $1/2$ and degree $6$. Then both the infinite product $\prod_{p \notin SQ} (\text{Euler}_p(N(p)^{-s}))^{-1}$ and its dual analogue are differentiable on the open half-plane $\{s : \mathrm{Re}\,s > 1\}$ given by the abscissa of the datum.
--
--   This is the holomorphy statement, to the right of the abscissa of convergence, for the partial Rankin–Selberg $L$-function attached to a $\mathrm{GL}(2)$ Hecke eigensystem over $\mathbb{Q}$ and a character of the ideles of a cubic field, together with its dual; it is the analytic input for the subsequent construction of an entire completed $L$-function bounded on vertical strips in the Langlands–Tunnell part of the argument. It is deduced from the convergence of the corresponding Euler product under the same first-moment and Satake-root bounds, together with the convergence of $\sum_v N(v)^{-\sigma}$ for $\sigma > 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal
open scoped Classical in

theorem LanglandsTunnell.RankinSelberg.differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (gammaR gammaC gammaRDual gammaCDual : Multiset ℂ)
    (hμ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Pi.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Pi.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (hroot : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ γ δ : ℂ, γ + δ = Pi.a p ∧ γ * δ = Pi.b p ∧
      ‖γ‖ < Real.sqrt (Ideal.absNorm p.asIdeal) ∧ ‖δ‖ < Real.sqrt (Ideal.absNorm p.asIdeal)) :
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFun
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} ∧
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFunDual
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} := by sorry
