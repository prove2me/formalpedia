-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable
-- name    : LanglandsTunnell.RankinSelberg.exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/1bb219da-b3b2-57e3-9b9c-32200c5eecad
-- title:
--   Unfolding the GL₂timesGL₂ Rankin–Selberg integral
-- statement:
--   Fix a number field $F$, a Haar measure $\nu_0$ on the idele group $(\mathbb{A}_F)^\times$, a set $D_p \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family of subgroups $U$ indexed by ideals of $\mathcal{O}_F$, a family $\mathrm{gen}$ of elements indexed by the height-one primes, an additive character $\psi$ of $\mathbb{A}_F$ that is trivial on $F$, continuous and non-trivial and satisfies $\|\psi(x)\| = 1$ for all $x$, and reals $0 < e_1 < e_2$. Then there is $C > 0$, depending only on these data, such that the following holds for all idele characters $\mu, \nu, \omega, \omega'$ with $\mu, \nu$ trivial on the principal ideles, unitary and continuous and $\omega\omega'\mu\nu = 1$; all $\Phi$ in the span of the pure tensors of Schwartz functions on the infinite part with locally constant compactly supported functions on $(\mathbb{A}_{F,\mathrm{fin}})^2$; all continuous $\varphi, \varphi' : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ invariant under left translation by $\mathrm{GL}_2(F)$ and transforming under the central scalars by $\omega$, respectively $\omega'$; all $s$ with $\operatorname{Re} s > 0$; and all $D \subseteq \{g : \|\det g\| \in [e_1, e_2]\}$ that is a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$ restricted to that slab. Here the Whittaker coefficients are $W^{\psi}_{\varphi}(a, g) = \int \varphi(n(x)g)\,\psi(-\alpha_a x)\,d\nu(x)$ with $n(x) = \begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, $\alpha_a$ the image of $a \in F$ in $\mathbb{A}_F$, and $\nu$ the adelic Haar measure conditioned on the adelic box (the carrier data $D_p$, $U$, $\mathrm{gen}$ entering only through this package of pins). The further hypotheses are: absolute summability over $a \in F$ of $W^{\psi}_{\varphi}(a, g)$ and of $W^{\psi^{-1}}_{\varphi'}(a, g)$ at every $g$; vanishing of $W^{\psi^{-1}}_{\varphi'}(0, g)$ for every $g$; absolute summability over $\xi \in F$ of the Bruhat series of the Godement section $f_s(g) = \mu(\det g)\,|\det g|^{s+1/2}\int \Phi(t \cdot (\text{bottom row of } g))\,(\mu\nu^{-1})(t)\,\|t\|^{2s+1}\,d\nu_0(t)$ at $w\,n(\xi)\,g$, both for $g \in D$ and at every $g$, where $w$ is the Weyl element; integrability on $D$ of $\|\varphi\varphi'\|$ times the sum of $\|f_s\|$ and of that series; and integrability over the quotient of $\mathrm{GL}_2(\mathbb{A}_F)$ by the adelic unipotent subgroup, for the associated quotient measure, of $\|W^{\psi}_{\varphi}(1, \cdot)\,W^{\psi^{-1}}_{\varphi'}(1, \cdot)\,K_s\|$, where $K_s(g) = \mu(\det g)\,|\det g|^{s+1/2}\,\Phi(\text{bottom row of } g)$. The conclusion is $$\int_D \varphi(g)\,\varphi'(g)\,E_s(g)\,dg = C \int W^{\psi}_{\varphi}(1, q)\,W^{\psi^{-1}}_{\varphi'}(1, q)\,K_s(q)\,dq,$$ the outer integral being over the unipotent quotient and $E_s = f_s + \sum_{\xi \in F} f_s(w\,n(\xi)\,\cdot)$ the Godement–Eisenstein series. Here $|\cdot|$ denotes the character $x \mapsto \alpha(x)^{\bullet}$ built from the module of the ideles.
--
--   This is the unfolding step of the Rankin–Selberg method for $\mathrm{GL}_2 \times \mathrm{GL}_2$: the period of a product of two automorphic functions against a Godement–Eisenstein series on a determinant slab is identified, up to an explicit positive constant, with an integral of the product of their Whittaker coefficients against the Godement kernel over the unipotent quotient. It feeds the statement [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), where the resulting Whittaker integral is expanded as an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg
open AutomorphicForm

theorem LanglandsTunnell.RankinSelberg.exists_rs22GlobalIntegral_godementEisenstein_eq_mul_rs22WhittakerIntegral_of_isUnitaryChar_of_re_pos_of_forall_summable_of_integrable
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (Dp : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ) (_hψu : ∀ x : AdeleRing (𝓞 F) F, ‖ψ x‖ = 1)
    (e₁ e₂ : ℝ) (_he₁ : 0 < e₁) (_he : e₁ < e₂) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsIdeleClassChar (𝓞 F) F μ) (_hν : IsIdeleClassChar (𝓞 F) F ν)
      (_hμu : IsUnitaryChar (𝓞 F) F μ) (_hνu : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hωμν : ω * ω' * μ * ν = 1)
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F)
      (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (_hφc : Continuous φ) (_hφ'c : Continuous φ')
      (_hφl : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
      (_hφ'l : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ' (globalPoints (𝓞 F) F γ * g) = φ' g)
      (_hφz : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
      (_hφ'z : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        φ' (centralScalar (𝓞 F) F z * g) = ((ω' z : ℂˣ) : ℂ) * φ' g)
      (_hφW : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun a : F =>
        ‖whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ φ a g‖)
      (_hφ'W : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun a : F =>
        ‖whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ⁻¹ φ' a g‖)
      (_hφ'0 : ∀ g : AdelicGL2 (𝓞 F) F,
        whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ⁻¹ φ' 0 g = 0)
      (s : ℂ) (_hs : 0 < s.re)
      (D : Set (AdelicGL2 (𝓞 F) F))
      (_hDs : D ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
      (_hD : IsFundamentalDomain (globalPoints (𝓞 F) F).range D
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
      (_hsum : ∀ g ∈ D, Summable fun ξ : F =>
        ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (_hsumAll : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (_hfold : IntegrableOn (fun g : AdelicGL2 (𝓞 F) F => ‖φ g * φ' g‖ *
          (‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s g‖ +
            ∑' ξ : F, ‖godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s
              (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖))
        D (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hunf : Integrable (fun q : UnipotentQuotient F =>
          ‖whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ φ 1 q.out *
            whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ⁻¹ φ' 1 q.out *
            rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s q.out‖)
        (unipotentQuotientMeasure F)),
      rs22GlobalIntegral F D φ φ' (godementEisenstein F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s) =
        (C : ℂ) * rs22WhittakerIntegral F
          (whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ φ 1)
          (whittakerCoefficient F (productionPinsOf F Dp U gen (adelicBox F)) ψ⁻¹ φ' 1)
          μ (moduleChar F) (moduleChar_pos F) Φ s := by sorry
