-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
-- name    : LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/0b3aad8f-acbe-5373-9ea9-63780158ea4d
-- title:
--   Entirety and vertical boundedness of the GL₂× GL₂ global integral
-- statement:
--   Let $F$ be a number field, $c,u$ real numbers with $0<c$, and let $G=GL_2(\mathbb A_F)$, carrying the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`. Write $S(c,u)\subseteq G$ for the integrally windowed Siegel set `integralWindowedSiegelSet F c u`, consisting of those $g$ whose finite part lies in the full integral subgroup `finiteIntegralGL2`, whose archimedean height $\prod_v \mathrm{localHeight}(g_v)^{[F_v:\mathbb R]}$ is at least $c$, and for which $\mathrm{xWindowSq}(g_v)\le u^2$ at every infinite place $v$. Assume given a finite set `tset` of elements of $G$ and a measurable set $\mathcal F\subseteq G$ of finite Haar measure contained in the union of the right translates $S(c,u)\,t$ for $t\in$ `tset`. Let $\varphi,\varphi'\colon G\to\mathbb C$ be continuous and rapidly decreasing on Siegel sets, i.e. for all $c'>0$, $u'$, all $t\in G$ and all $N\in\mathbb N$ the quantity $\|\varphi(gt)\|(1+\mathrm{archHeight}(g))^N$ is bounded for $g\in S(c',u')$, and likewise for $\varphi'$. Let $H\colon\mathbb C\times G\to\mathbb C$ be jointly continuous, entire in the first variable for each fixed $g$, and uniformly Siegel bounded: for all $\sigma_1,\sigma_2,c'>0,u'$ and $t\in G$ there are $A\in\mathbb R$, $N\in\mathbb N$ with $\|H(s,gt)\|\le A(1+\mathrm{archHeight}(g))^N$ for all $s$ with $\sigma_1\le\Re s\le\sigma_2$ and all $g\in S(c',u')$. The conclusion is threefold: for every $s$ the function $g\mapsto \varphi(g)\varphi'(g)H(s,g)$ is Haar-integrable on $\mathcal F$; the function $s\mapsto \int_{\mathcal F}\varphi(g)\varphi'(g)H(s,g)\,dg$ is entire; and it is bounded on every vertical strip, i.e. for all $a\le b$ there is $C$ bounding its modulus on $a\le\Re s\le b$.
--
--   This is the analytic half of the theory of Jacquet's global $GL_2\times GL_2$ Rankin–Selberg integral: the pairing of two cusp-form-like functions against a family of Eisenstein kernels is holomorphic in $s$ and bounded in vertical strips, once the kernel grows at most polynomially in the archimedean height uniformly on strips. It is used in the construction of the Rankin–Selberg $L$-datum, being cited by [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), where the kernel is the pole-free part of a Godement–Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_HonestLDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm AutomorphicForm.WindowedSiegel
open NumberField.AdelicHaar NumberField.AdelicLevel LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.integrableOn_and_differentiable_and_boundedOnStrips_rs22GlobalIntegral_of_isUniformlySiegelBounded
    (F : Type) [Field F] [NumberField F]
    (c u : ℝ) (hc : 0 < c) (tset : Finset (AdelicGL2 (𝓞 F) F))
    (𝓕 : Set (AdelicGL2 (𝓞 F) F)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕μ : adelicGLHaar (Fin 2) (𝓞 F) F 𝓕 < ⊤)
    (h𝓕S : 𝓕 ⊆ ⋃ t ∈ tset, (· * t) '' integralWindowedSiegelSet F c u)
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ'c : Continuous φ')
    (hφ : IsRapidlyDecreasingOnSiegelSets F φ) (hφ' : IsRapidlyDecreasingOnSiegelSets F φ')
    (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hHd : ∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g))
    (hHc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2)
    (hHb : IsUniformlySiegelBounded F H) :
    (∀ s : ℂ, IntegrableOn (fun g => φ g * φ' g * H s g) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
    Differentiable ℂ (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) ∧
    LanglandsTunnell.LDatum.BoundedOnStrips (fun s : ℂ => rs22GlobalIntegral F 𝓕 φ φ' (H s)) := by sorry
