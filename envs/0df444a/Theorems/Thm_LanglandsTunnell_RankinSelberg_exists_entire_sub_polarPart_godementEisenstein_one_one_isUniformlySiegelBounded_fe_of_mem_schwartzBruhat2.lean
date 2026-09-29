-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
-- name    : LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/746fabf0-200b-5c4a-b4b9-52b45f0331f9
-- title:
--   Polar decomposition and functional equation of (1,1) Godement–Eisenstein series
-- statement:
--   Let $F$ be a number field, with measurable and Borel structures on the adele ring $\mathbb{A}_F$ and on its unit group, a Haar measure $\nu_0$ on the ideles, an additive Haar measure $\mu_1$ on $\mathbb{A}_F$ normalised by $\mu_1(\mathrm{adelicBox}\,F)=1$, and an additive character $\psi$ of $\mathbb{A}_F$ which is trivial on principal adeles, continuous and nontrivial. Write $\alpha=$ `moduleChar F` for the real-valued module character of the idele group coming from `distribHaarChar`; it is assumed that $\alpha(x)>0$ for all $x$ and that $\alpha$ is trivial on principal ideles. Let $\Phi$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the pure tensors $g\otimes h$ with $g$ Schwartz on pairs of vectors in the mixed space of $F$ and $h$ locally constant of compact support on pairs of finite adeles. Then there exist $R,R':\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, a function $X$ on $\mathrm{GL}_2(\mathbb{A}_F)$, and constants $w,c_1,c_0\in\mathbb{C}$ with: $s\mapsto R\,s\,g$ and $s\mapsto R'\,s\,g$ entire for each $g$; both jointly continuous in $(s,g)$; both uniformly Siegel bounded, i.e. for all $\sigma_1,\sigma_2,c,u$ with $c>0$ and all $t$ there are $A$ and $N$ with $\|R\,s\,(gt)\|\le A(1+\mathrm{archHeight}(g_\infty))^N$ for $\sigma_1\le \operatorname{re}s\le\sigma_2$ and $g$ in the integral windowed Siegel set of parameters $c,u$; $X$ continuous, $\operatorname{re}w=0$ and $X(g)=\alpha(\det g)^{w}$ via `cpowChar`; for $\operatorname{re}s>1/2$ and all $g$, the Godement–Eisenstein series of $\Phi$ at the pair of trivial characters, $\mathrm{godementEisenstein}\,F\,\nu_0\,1\,1\,\alpha\,h_\alpha\,\Phi$ (the Godement section $\alpha(\det g)^{s+1/2}$ times Tate's global zeta integral of $t\mapsto\Phi(t\cdot(\text{bottom row of }g))$ at $2s+1$, plus the sum of its translates by $w_0u(\xi)$ over $\xi\in F$), equals $R\,s\,g+(c_1/(s-1/2)+c_0/(s+1/2))X(g)$; the same series for `reflectPair ψ μ₁ Φ`, namely $x\mapsto\widehat\Phi(x_1,-x_0)$ with the Fourier transform taken for `pairChar ψ` and `pairHaar μ₁`, equals $R'\,s\,g-(c_1/(s+1/2)+c_0/(s-1/2))X(g)$ there; and $R\,s\,g=R'\,(-s)\,g$ for all $s,g$.
--
--   This is the analytic continuation of the $\mathrm{GL}_2$ Godement–Eisenstein series attached to a Schwartz–Bruhat function of two adelic variables, specialised to the pair of trivial idele class characters, so that the only poles are the simple ones at $s=\pm 1/2$ with residues proportional to a unitary character $\alpha(\det g)^{w}$, together with the functional equation relating $\Phi$ and its reflected Fourier transform. It feeds the Rankin–Selberg package [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), where the uniform Siegel bounds are what allow the Eisenstein series to be integrated against cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell.RankinSelberg
open scoped NNReal

theorem LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_one_one_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    (_hμ₁ : μ₁ (adelicBox F) = 1)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
    (hα : ∀ x, 0 < ((moduleChar F x : ℝˣ) : ℝ))
    (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) (moduleChar F))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ (R R' : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (X : AdelicGL2 (𝓞 F) F → ℂ) (w c₁ c₀ : ℂ),
      (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => R s g)) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => R' s g)) ∧
      (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => R p.1 p.2) ∧
      (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => R' p.1 p.2) ∧
      IsUniformlySiegelBounded F R ∧ IsUniformlySiegelBounded F R' ∧
      Continuous X ∧ w.re = 0 ∧
      (∀ g : AdelicGL2 (𝓞 F) F,
        X g = ((cpowChar (moduleChar F) hα w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ 1 1 (moduleChar F) hα Φ s g =
          R s g + (c₁ / (s - 1 / 2) + c₀ / (s + 1 / 2)) * X g) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ 1 1 (moduleChar F) hα (reflectPair ψ μ₁ Φ) s g =
          R' s g - (c₁ / (s + 1 / 2) + c₀ / (s - 1 / 2)) * X g) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), R s g = R' (-s) g) := by sorry
