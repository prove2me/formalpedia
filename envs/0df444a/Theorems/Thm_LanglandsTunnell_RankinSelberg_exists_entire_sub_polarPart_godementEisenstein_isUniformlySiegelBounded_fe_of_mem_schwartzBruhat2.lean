-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
-- name    : LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/42748538-fa3a-53c4-8fd1-e8d3a5285f40
-- title:
--   Polar decomposition and functional equation of Godement–Eisenstein series
-- statement:
--   Let $F$ be a number field, with the idele group $(\mathbb{A}_F)^\times$ and the adele ring $\mathbb{A}_F$ carrying Borel measurable structures, let $\nu_0$ be a Haar measure on $(\mathbb{A}_F)^\times$ and $\mu_1$ an additive Haar measure on $\mathbb{A}_F$ normalised so that the adelic box (infinite box times the integral finite adeles) has measure $1$; let $\psi$ be an additive character of $\mathbb{A}_F$ which is invariant under the principal adeles, continuous and nontrivial. Write $\alpha =$ `moduleChar F` for the module character of the ideles, obtained from the distributive Haar character of $\mathbb{A}_F$; it is assumed positive, $\alpha(x) > 0$ for all $x$, and trivial on the image of $F^\times$. Let $\mu,\nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be monoid homomorphisms which are unitary ($|\mu(x)| = |\nu(x)| = 1$), trivial on the principal ideles, and continuous, and let $\Phi$ lie in the span of the pure tensors of Schwartz functions at the infinite places with locally constant compactly supported functions at the finite places, in two adelic variables. The assertion is the existence of $R, R' : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, a function $X$ on $\mathrm{GL}_2(\mathbb{A}_F)$ and complex numbers $w, c_1, c_0, p_1, p_0$ with: $s \mapsto R\,s\,g$ and $s \mapsto R'\,s\,g$ differentiable on all of $\mathbb{C}$ for each $g$; $(s,g) \mapsto R\,s\,g$ and $(s,g)\mapsto R'\,s\,g$ continuous; $R$ and $R'$ uniformly Siegel bounded, i.e. for all reals $\sigma_1,\sigma_2,c,u$ with $c>0$ and every $t \in \mathrm{GL}_2(\mathbb{A}_F)$ there are $A \in \mathbb{R}$ and $N \in \mathbb{N}$ with $\|R\,s\,(gt)\| \le A(1 + \mathrm{archHeight}(g))^N$ whenever $\sigma_1 \le \mathrm{Re}\,s \le \sigma_2$ and $g$ lies in the integrally windowed Siegel set of parameters $c,u$ (likewise for $R'$); $X$ continuous, $\mathrm{Re}\,w = 0$ and $X(g) = \mu(\det g)\,\alpha(\det g)^{w}$; the vanishing $c_1 = c_0 = 0$ whenever $\mu\nu^{-1}$ differs from $x \mapsto \|x\|^{i\tau}$ for every real $\tau$; for $\mathrm{Re}\,s > 1/2$ and all $g$ the Godement–Eisenstein series of $\Phi$ at $(\mu,\nu)$ — the Godement section plus the sum over $\xi \in F$ of the section at $w\,n(\xi)\,g$ — equals $R\,s\,g + \bigl(c_1/(s-p_1) + c_0/(s-p_0)\bigr)X(g)$, while the same series formed from the reflected function $x \mapsto \widehat{\Phi}(x_1,-x_0)$ (Fourier transform with respect to $\psi$ and $\mu_1$) at the pair $(\nu,\mu)$ equals $R'\,s\,g - \bigl(c_1/(s+p_1) + c_0/(s+p_0)\bigr)X(g)$; and finally $R\,s\,g = R'\,(-s)\,g$ for all $s$ and $g$.
--
--   This is the meromorphic continuation and functional equation of the Eisenstein series attached to a Godement section on $\mathrm{GL}_2$ over a number field: the series is an entire family, bounded on vertical strips uniformly over translated Siegel sets, plus at most two simple polar terms whose residues are multiples of a single unitary character of the determinant, the poles occurring only when $\mu\nu^{-1}$ is a purely imaginary power of the idele norm. It feeds the Rankin–Selberg integral of the Langlands–Tunnell step, being used in the identification of the global integral with an Euler product together with its polar contribution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2.lean

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
    LanglandsTunnell.RankinSelberg.exists_entire_sub_polarPart_godementEisenstein_isUniformlySiegelBounded_fe_of_mem_schwartzBruhat2
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
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ μ ν (moduleChar F) hα Φ s g =
          R s g + (c₁ / (s - p₁) + c₀ / (s - p₀)) * X g) ∧
      (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        godementEisenstein F ν₀ ν μ (moduleChar F) hα (reflectPair ψ μ₁ Φ) s g =
          R' s g - (c₁ / (s + p₁) + c₀ / (s + p₀)) * X g) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), R s g = R' (-s) g) := by sorry
