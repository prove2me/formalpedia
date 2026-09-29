-- Prove2me | Theorems.Thm_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
-- name    : NumberField.TateGlobal.zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/c4db5d51-500f-5498-89e8-d998f680cb2c
-- title:
--   Entire continuation and functional equation of Tate's zeta integral
-- statement:
--   Let $F$ be a number field, let $\nu$ be a Haar measure on the idele group $(\mathbb{A}_F)^\times$ and $\mu$ an additive Haar measure on the adele ring $\mathbb{A}_F$ normalised so that $\mu$ of the adelic box — the adeles whose infinite component lies in the preimage, under the identification of $\mathbb{A}_{F,\infty}$ with the mixed space of $F$, of the fundamental domain of the canonical lattice basis, and whose finite component is integral at every finite place — equals $1$. Let $\psi$ be an additive character of $\mathbb{A}_F$ which is trivial on $F$, continuous and non-trivial, and whose restriction to the infinite adeles is $x \mapsto e^{2\pi i\,\mathrm{Tr}_{\mathbb{R}}(x)}$ via the mixed-space trace. Let $f$ lie in the Schwartz–Bruhat space, the $\mathbb{C}$-span of products $g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space and $h$ locally constant of compact support on the finite adeles. Let $\chi : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be a continuous homomorphism with $\lVert \chi(x)\rVert = 1$ for all $x$, trivial on the principal ideles $F^\times$, and non-trivial at some element of the norm-one ideles, that is, of the kernel of the distributive Haar character. Then there is a function $Z : \mathbb{C} \to \mathbb{C}$, differentiable everywhere, such that $Z(s) = \int f(x)\chi(x)\lVert x\rVert^{s}\,d\nu$ for $\operatorname{Re} s > 1$, such that $Z(1-s)$ equals the same integral formed from the Fourier transform $\widehat{f}(w) = \int \psi(-vw)f(v)\,d\mu$ and from $\chi^{-1}$ at $s$ for $\operatorname{Re} s > 1$, and such that for every pair of reals $\sigma_1, \sigma_2$ there is a constant $C$ with $\lVert Z(s)\rVert \le C$ whenever $\sigma_1 \le \operatorname{Re} s \le \sigma_2$. Here $\lVert x \rVert$ denotes the idele norm, the value of the distributive Haar character of $\mathbb{A}_F$ at $x$.
--
--   This is the main analytic theorem of Tate's thesis in the case of a unitary idele class character that is non-trivial on the norm-one ideles: the zeta integral, convergent for $\operatorname{Re} s > 1$, extends to an entire function bounded in vertical strips and satisfying the functional equation relating $(f,\chi)$ to $(\widehat f, \chi^{-1})$. It underlies the Euler product and Gamma-factor descriptions of Hecke $L$-functions in this development and, through them, the Hecke-character input to the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.TateGlobal.zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (_hμ1 : μ (adelicBox F) = 1)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
    (_hψinf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    {f : AdeleRing (𝓞 F) F → ℂ} (_hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 F) F χ) (_hχF : IsIdeleClassChar (𝓞 F) F χ)
    (_hχ1 : ∃ x ∈ normOneIdeles F, χ x ≠ 1) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z
      ∧ (∀ s : ℂ, 1 < s.re → Z s = zetaIntegral ν f χ s)
      ∧ (∀ s : ℂ, 1 < s.re → Z (1 - s) = zetaIntegral ν (fourierIntegral ψ μ f) χ⁻¹ s)
      ∧ (∀ σ₁ σ₂ : ℝ, ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖Z s‖ ≤ C) := by sorry
