-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
-- name    : LanglandsTunnell.RankinSelberg.integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/faeb0a46-bf4e-5803-a4cd-e99865f747dd
-- title:
--   Integrability of the unfolded Rankin–Selberg integrand, primal and dual
-- statement:
--   Fix a set $D_p\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ indexed by ideals of $\mathbb{Z}$, and a family $\mathrm{gen}$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ indexed by the finite places; these assemble into the carrier pins `productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)`, whose measures are adelic Haar on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ for the Borel structure and, on $\mathbb{A}_{\mathbb{Q}}$, additive Haar conditioned on the adelic box, the central subgroup being $\top$. Two parallel assertions are made. In the first, let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ that is trivial on principal adeles, continuous and non-trivial; let $\Theta, W:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, with $W$ gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing off a root-level region, with decay in the root-size product and the archimedean root sum), satisfying $W(u(x,y,z)g)=\psi(x+y)W(g)$ for the upper unipotent $u(x,y,z)$, expanding $\Theta$ in the sense that for every $g$ the family $i\mapsto W(\mathrm{mirabolicTranslate}(i)\,g)$ over $\mathrm{MirabolicIndex}\ \mathbb{Q}$ has sum $\Theta(g)$, and having the Whittaker half-plane property; let $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ be continuous, invariant under left translation by the global points of $\mathrm{GL}_2(\mathbb{Q})$, and subject to a bound $\|\varphi(g)\|\le C\,\|\det g\|^{r}$ for some real $C,r$; let $D$ be a fundamental domain for the global points acting on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with adelic Haar measure, and let $\sigma$ be a section of the projection of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ onto the quotient by the orbit relation of the adelic unipotent subgroup. Then there is $\sigma_0\in\mathbb{R}$ such that for every $s\in\mathbb{C}$ with $\operatorname{Re} s>\sigma_0$ the function $q\mapsto W^{\psi^{-1}}_{\varphi}(\sigma q)\,W(\iota(\sigma q))\,\|\det \sigma q\|^{s-1/2}$ is integrable on the unipotent quotient for the quotient measure, where $W^{\psi^{-1}}_{\varphi}$ is the Whittaker coefficient at $\alpha=1$ formed with $\psi^{-1}$ and the conditioned measure of the pins, $\iota$ the embedding $\mathrm{GL}_2\hookrightarrow\mathrm{GL}_3$ and $\|\det\cdot\|$ the idele norm of the determinant. The second assertion is the same with $W'$ a continuous gauge-majorised $\psi^{-1}$-Whittaker function whose mirabolic expansion sums to $g\mapsto\Theta({}^t g^{-1})$, paired with the Whittaker coefficient of $\varphi$ formed with $\psi$.
--
--   This is the convergence half of the Rankin–Selberg unfolding for a $\mathrm{GL}_2$ form against a $\mathrm{GL}_3$ Whittaker function, stated symmetrically for the given character and its inverse so that both the integral and its dual are covered. It supports the later identification of the global Rankin–Selberg integral as a product of archimedean and finite local integrals, and is cited by the two results that factorise `rsGlobalIntegral` over a finite family of archimedean data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow.lean

import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm
open LanglandsTunnell.CubicInduction LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.integrable_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hWc : Continuous W) (_hWg : IsGaugeMajorised3 ℚ W)
        (_hWlaw : IsGL3PsiWhittakerFn ψ W)
        (_hWexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Θ g))
        (_hWhp : HasWhittakerHalfPlane W)
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ φ 1 g *
                    W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hW'c : Continuous W') (_hW'g : IsGaugeMajorised3 ℚ W')
        (_hW'law : IsGL3PsiWhittakerFn ψ⁻¹ W')
        (_hW'exp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Θ g))
        (_hW'hp : HasWhittakerHalfPlane W')
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          Integrable (fun q : UnipotentQuotient ℚ => (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ φ 1 g *
                    W' (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q))
              (unipotentQuotientMeasure ℚ)) := by sorry
