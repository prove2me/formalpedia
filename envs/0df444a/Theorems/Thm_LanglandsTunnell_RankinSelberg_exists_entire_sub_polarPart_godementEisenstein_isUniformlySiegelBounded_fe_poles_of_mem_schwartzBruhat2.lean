-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_poles_of_mem_schwartzBruhat2
-- name    : LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_poles_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/4646a10a-336a-5d01-9945-856075e97eaa
-- title:
--   Godement–Eisenstein series: explicit poles, entire part, functional equation
-- statement:
--   Let $F$ be a number field, with Borel measurable structures on the adele ring $\mathbb{A}=\mathrm{AdeleRing}(\mathcal{O}_F,F)$ and on $\mathbb{A}^\times$, a Haar measure $\nu_0$ on $\mathbb{A}^\times$, and an additive Haar measure $\mu_1$ on $\mathbb{A}$ normalised by $\mu_1(\mathrm{adelicBox}\,F)=1$ (the box cut out by the infinite box and the integral finite adeles). Let $\psi$ be an additive character of $\mathbb{A}$ which is invariant under the principal adeles, continuous and nontrivial; let $\alpha=\mathrm{moduleChar}\,F$, the module character built from the distributive Haar character of $\mathbb{A}$, assumed positive on every idele and trivial on the principal ideles $F^\times$. Let $\mu,\nu:\mathbb{A}^\times\to\mathbb{C}^\times$ be continuous monoid homomorphisms of absolute value $1$ that are trivial on the image of $F^\times$, and let $\Phi$ lie in $\mathrm{schwartzBruhat2}\,F$, the $\mathbb{C}$-span of products of a Schwartz function in the two archimedean variables with a locally constant compactly supported function in the two finite-adelic variables. Then there are functions $R,R':\mathbb{C}\times\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$, a function $X$ on $\mathrm{GL}_2(\mathbb{A})$, and constants $w,c_1,c_0,p_1,p_0\in\mathbb{C}$ with: $s\mapsto R(s,g)$ and $s\mapsto R'(s,g)$ entire for each $g$; $R$ and $R'$ jointly continuous and uniformly Siegel-bounded in the sense of `IsUniformlySiegelBounded` (on each vertical strip $\sigma_1\le\operatorname{Re}s\le\sigma_2$ and each right translate by $t$ of an integral windowed Siegel set with parameters $c>0$, $u$, one has $\lVert R(s,gt)\rVert\le A(1+\mathrm{archHeight})^N$ for some $A$, $N$); $X$ continuous; $\operatorname{Re}w=0$ and $X(g)=\mu(\det g)\,\alpha(\det g)^w$; $c_1=c_0=0$ unless $\mu\nu^{-1}=\lVert\cdot\rVert^{i\tau}$ (that is, $\mathrm{normPowChar}\,F\,\tau$) for some real $\tau$, and for every real $\tau$ with $\mu\nu^{-1}=\lVert\cdot\rVert^{i\tau}$ one has $p_1=(1-i\tau)/2$ and $p_0=-(1+i\tau)/2$; for $\operatorname{Re}s>1/2$ and all $g$, the Godement–Eisenstein series $\mathrm{godementEisenstein}$ attached to $(\nu_0,\mu,\nu,\alpha,\Phi)$ — the Godement section plus the sum of its translates by $w_{\mathrm{adelic}}\,n(\xi)$ over $\xi\in F$ — equals $R(s,g)+\bigl(c_1/(s-p_1)+c_0/(s-p_0)\bigr)X(g)$, while the series attached to $(\nu_0,\nu,\mu,\alpha)$ and to $\mathrm{reflectPair}\,\psi\,\mu_1\,\Phi$ (the adelic Fourier transform of $\Phi$ read at $(x_1,-x_0)$) equals $R'(s,g)-\bigl(c_1/(s+p_1)+c_0/(s+p_0)\bigr)X(g)$; and $R(s,g)=R'(-s,g)$ for all $s$ and $g$.
--
--   This is the analytic continuation, growth estimate and functional equation of the Godement–Eisenstein (Eisenstein–Tate) series attached to a Schwartz–Bruhat function on $\mathbb{A}^2$ and a pair of unitary idele class characters, in the form used in the Rankin–Selberg theory of $\mathrm{GL}_2$: the series is an entire, uniformly Siegel-bounded family plus an explicit two-term polar part supported on the locus $\mu\nu^{-1}=\lVert\cdot\rVert^{i\tau}$, with the poles pinned at $(1-i\tau)/2$ and $-(1+i\tau)/2$. It feeds [`AutomorphicForm.exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2`](thm.html#AutomorphicForm.exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2), where the explicit pole locations allow multiplication by a quadratic factor to produce an entire family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_poles_of_mem_schwartzBruhat2.lean

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

theorem
    LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_poles_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    (_hμ₁ : μ₁ (adelicBox F) = 1)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
    (hα : ∀ x, 0 < ((moduleChar F x : ℝˣ) : ℝ))
    (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) (moduleChar F))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ (R R' : ℂ → AdelicGL2 (𝓞 F) F → ℂ) (X : AdelicGL2 (𝓞 F) F → ℂ) (w c₁ c₀ p₁ p₀ : ℂ),
      (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => R s g)) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => R' s g)) ∧
      (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => R p.1 p.2) ∧
      (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => R' p.1 p.2) ∧
      IsUniformlySiegelBounded F R ∧ IsUniformlySiegelBounded F R' ∧
      Continuous X ∧ w.re = 0 ∧
      (∀ g : AdelicGL2 (𝓞 F) F,
        X g = ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
          ((cpowChar (moduleChar F) hα w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)) ∧
      ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) → c₁ = 0 ∧ c₀ = 0) ∧
      (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
        p₁ = ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2 ∧ p₀ = -((1 : ℂ) + (τ : ℂ) * Complex.I) / 2) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s g =
          R s g + (c₁ / (s - p₁) + c₀ / (s - p₀)) * X g) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ ν μ (moduleChar F) hα (reflectPair ψ μ₁ Φ) s g =
          R' s g - (c₁ / (s + p₁) + c₀ / (s + p₀)) * X g) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), R s g = R' (-s) g) := by sorry
