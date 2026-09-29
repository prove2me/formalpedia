-- Prove2me | Theorems.Thm_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
-- name    : NumberField.TateGlobal.zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/9ba996ed-0ad2-504e-aa60-70df3a09b506
-- title:
--   Entire continuation and functional equation of Tate's zeta integral
-- statement:
--   Let $F$ be a number field, with Borel measurable structures fixed on its adele ring $\mathbb{A}_F$ and on the idele group $\mathbb{A}_F^\times$, let $\nu$ be a Haar measure on $\mathbb{A}_F^\times$ and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$ normalised so that the adelic box — the set of adeles whose infinite component is carried by the identification with the mixed space into the fundamental domain of the lattice basis of $F$, and whose finite component is integral at every finite place — has measure $1$. Let $\psi$ be a $\mathbb{C}$-valued additive character of $\mathbb{A}_F$ which is continuous, non-trivial and trivial on every principal adele $\alpha \in F$, and whose restriction to the infinite adeles is $x \mapsto e^{2\pi i \operatorname{Tr}_{\mathbb{R}}(x)}$, the trace being taken in the mixed space. Let $f$ lie in the Schwartz–Bruhat space, the $\mathbb{C}$-span of the products $x \mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space and $h$ locally constant with compact support on the finite adeles. Let $\chi : \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a continuous homomorphism with $\lvert\chi(x)\rvert = 1$ for all $x$, trivial on the principal ideles $F^\times$, and assume there is an $x$ in the kernel of the module character $\operatorname{distribHaarChar}$ of $\mathbb{A}_F$ (the norm-one ideles) with $\chi(x) \neq 1$. Then there exists an entire $Z : \mathbb{C} \to \mathbb{C}$ such that for every $s$ with $\operatorname{Re} s > 1$ one has $Z(s) = \int_{\mathbb{A}_F^\times} f(x)\chi(x)\lVert x\rVert^{s}\,d\nu(x)$ and $Z(1-s) = \int_{\mathbb{A}_F^\times} \hat f(x)\chi^{-1}(x)\lVert x\rVert^{s}\,d\nu(x)$, where $\lVert\cdot\rVert$ is the real value of $\operatorname{distribHaarChar}$ and $\hat f(w) = \int \psi(-(vw))f(v)\,d\mu(v)$.
--
--   This is the case of Tate's main theorem on global zeta integrals in which no poles occur: when $\chi$ is non-trivial on the norm-one ideles, the zeta integral extends to an entire function satisfying the functional equation relating $f$ at $s$ to its adelic Fourier transform at $1-s$. It is used to obtain an entire continuation of the partial Euler product attached to such a character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.TateGlobal.zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
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
      ∧ (∀ s : ℂ, 1 < s.re → Z (1 - s) = zetaIntegral ν (fourierIntegral ψ μ f) χ⁻¹ s) := by sorry
