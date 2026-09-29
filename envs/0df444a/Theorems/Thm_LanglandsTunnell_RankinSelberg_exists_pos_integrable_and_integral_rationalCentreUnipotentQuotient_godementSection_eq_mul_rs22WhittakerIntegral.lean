-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
-- name    : LanglandsTunnell.RankinSelberg.exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/3b048f6a-e551-53ef-b8cf-2b40b2cfc763
-- title:
--   Unfolding the Godement section over Z(F)N(A)backslashGL₂(A)
-- statement:
--   Let $F$ be a number field, with the idele units $(\mathbb A_F)^\times$ and $\mathrm{GL}_2(\mathbb A_F)$ carrying their Borel structures, let $\nu_0$ be a Haar measure on $(\mathbb A_F)^\times$, and let $0 < e_1 < e_2$ be reals. The assertion is that there exists $C > 0$, depending only on these data, such that the following holds for every quadruple of monoid homomorphisms $\mu,\nu,\omega,\omega' : (\mathbb A_F)^\times \to \mathbb C^\times$ with $\omega\omega'\mu\nu = 1$ and with $\mu,\nu$ continuous as $\mathbb C$-valued functions, every measurable $\Phi : \mathbb A_F^2 \to \mathbb C$, every $s \in \mathbb C$, and every pair of measurable $W,W' : \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ such that (i) $W(zg)W'(zg) = \omega(z)\omega'(z)\,W(g)W'(g)$ for all central scalars $z \in (\mathbb A_F)^\times$ and all $g$, (ii) $W(ng)W'(ng) = W(g)W'(g)$ for all $n$ in the adelic unipotent subgroup (the range of `unipotentGL2Hom` over $\mathbb A_F$) and all $g$, and (iii) the function $q \mapsto \|W(q^{\mathrm{out}})W'(q^{\mathrm{out}})\,\mu(\det q^{\mathrm{out}})\,\|\det q^{\mathrm{out}}\|^{s+1/2}\,\Phi(\text{bottom row of } q^{\mathrm{out}})\|$, formed from chosen representatives $q^{\mathrm{out}}$, is integrable on the orbit quotient of $\mathrm{GL}_2(\mathbb A_F)$ by the adelic unipotent subgroup for the quotient measure `unipotentQuotientMeasure`, where $\|\cdot\|^{s+1/2}$ means the complex power `cpowChar` of the module character `moduleChar` of $\mathbb A_F$. The conclusion is twofold. First, on the orbit quotient $Z(F)N(\mathbb A_F)\backslash\mathrm{GL}_2(\mathbb A_F)$, namely the quotient of $\mathrm{GL}_2(\mathbb A_F)$ by the subgroup `rationalCentreUnipotent` with the quotient measure `rationalCentreUnipotentQuotientMeasure` built from the adelic $\mathrm{GL}_2$ Haar measure, the function $q \mapsto \mathbf 1_{\{\,e_1 \le \|\det g\| \le e_2\,\}}(q^{\mathrm{out}})\,W(q^{\mathrm{out}})W'(q^{\mathrm{out}})\,f_s(q^{\mathrm{out}})$ is integrable, where the idele norm is the distributive Haar character of $\mathbb A_F$ and $f_s(g) = \mu(\det g)\,\|\det g\|^{s+1/2}\,Z_{\nu_0}(t \mapsto \Phi(\text{bottom row of } g \cdot t),\,\mu\nu^{-1},\,2s+1)$ is the Godement section, the last factor being the global Tate zeta integral against $\nu_0$. Second, the integral of this function equals $C$ times `rs22WhittakerIntegral`, i.e. $C$ times the integral over the unipotent quotient of $W W'$ against the kernel $\mu(\det)\,\|\det\|^{s+1/2}\,\Phi(\text{bottom row evaluated at }1)$.
--
--   This is the second step of the Godement–Jacquet unfolding of the global $\mathrm{GL}_2 \times \mathrm{GL}_2$ Rankin–Selberg integral: having descended to $Z(F)N(\mathbb A)\backslash\mathrm{GL}_2(\mathbb A)$, the Tate integral inside the Godement section is absorbed, up to an explicit positive constant coming from the slab $e_1 \le \|\det\| \le e_2$ and the rational centre, into the Whittaker integral over $N(\mathbb A)\backslash\mathrm{GL}_2(\mathbb A)$. It feeds the identification of the Rankin–Selberg global integral against the Godement–Eisenstein series with the Whittaker integral, used in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicFourier IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.exists_pos_integrable_and_integral_rationalCentreUnipotentQuotient_godementSection_eq_mul_rs22WhittakerIntegral
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (μ ν ω ω' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hωμν : ω * ω' * μ * ν = 1)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦm : Measurable Φ)
      (s : ℂ)
      (W W' : AdelicGL2 (𝓞 F) F → ℂ) (_hWm : Measurable W) (_hW'm : Measurable W')
      (_hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        W (centralScalar (𝓞 F) F z * g) * W' (centralScalar (𝓞 F) F z * g) =
          ((ω z : ℂˣ) : ℂ) * ((ω' z : ℂˣ) : ℂ) * (W g * W' g))
      (_hN : ∀ (n : adelicUnipotent F) (g : AdelicGL2 (𝓞 F) F),
        W ((n : AdelicGL2 (𝓞 F) F) * g) * W' ((n : AdelicGL2 (𝓞 F) F) * g) = W g * W' g)
      (_hunf : Integrable (fun q : UnipotentQuotient F =>
          ‖W q.out * W' q.out * rs22Kernel F μ (moduleChar F) (moduleChar_pos F) Φ s q.out‖)
        (unipotentQuotientMeasure F)),
      Integrable (fun q : RationalCentreUnipotentQuotient F =>
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out)
        (rationalCentreUnipotentQuotientMeasure F) ∧
      ∫ q : RationalCentreUnipotentQuotient F,
          ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}.indicator
              (fun _ => (1 : ℂ)) q.out) *
            (W q.out * W' q.out) *
            godementSection F ν₀ μ ν (moduleChar F) (moduleChar_pos F) Φ s q.out
          ∂(rationalCentreUnipotentQuotientMeasure F) =
        (C : ℂ) * rs22WhittakerIntegral F W W' μ (moduleChar F) (moduleChar_pos F) Φ s := by sorry
