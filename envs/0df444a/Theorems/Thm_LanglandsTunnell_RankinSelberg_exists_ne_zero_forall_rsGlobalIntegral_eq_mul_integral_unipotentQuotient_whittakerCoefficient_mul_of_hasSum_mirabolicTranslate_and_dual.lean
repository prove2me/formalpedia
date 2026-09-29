-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
-- name    : LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/234cb2a0-0df0-575b-920f-90b7855df0c6
-- title:
--   Two-sided unfolding of the GL₂timesGL₃ Rankin–Selberg integral
-- statement:
--   Fix a set $D_p \subseteq \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ indexed by ideals of $\mathbb{Z}$, and a family $\mathrm{gen}$ of elements indexed by the finite places; these assemble, via `productionPinsOf` with the box `AdelicBox.adelicBox ℚ`, into the normalisation data used for the Whittaker coefficient, whose additive measure is the adelic additive Haar measure conditioned on that box. Then there is a nonzero $c \in \mathbb{C}$, independent of everything below, such that two identities hold. First: for every additive character $\psi$ of $\mathbb{A}_\mathbb{Q}$ that is trivial on $\mathbb{Q}$, continuous and nontrivial, every continuous $\Theta, W$ on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ with $W$ gauge-majorised in the sense of `IsGaugeMajorised3` (supported in a root-level set and rapidly decaying there), satisfying $W(u(x,y,z)g) = \psi(x+y)W(g)$ for all upper unipotent $u(x,y,z)$, satisfying the mirabolic expansion $\sum_{i} W(\iota(\gamma_i) g) = \Theta(g)$ as a convergent sum over $i \in N_2(\mathbb{Q})\backslash \mathrm{GL}_2(\mathbb{Q})$, and having a Whittaker half-plane of absolute convergence, every continuous $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ invariant under left translation by $\mathrm{GL}_2(\mathbb{Q})$ with $\|\varphi(g)\|\,\|\det g\|^{-1/2}$ bounded, every fundamental domain $D$ for the left action of $\mathrm{GL}_2(\mathbb{Q})$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ with respect to adelic Haar measure, and every section $\sigma$ of the quotient map onto $N_2(\mathbb{A})\backslash\mathrm{GL}_2(\mathbb{A})$, there exists $\sigma_0$ with $$\int_D \varphi(g)\,\Theta(\iota g)\,\|\det g\|^{s-1/2}\,dg = c\int_{N_2(\mathbb{A})\backslash\mathrm{GL}_2(\mathbb{A})} W^{\psi^{-1}}_{\varphi,1}(\sigma(q))\,W(\iota\,\sigma(q))\,\|\det \sigma(q)\|^{s-1/2}\,dq$$ for $\mathrm{Re}\,s > \sigma_0$, where $W^{\psi^{-1}}_{\varphi,1}$ is the Whittaker coefficient of $\varphi$ at $\alpha = 1$ against $\psi^{-1}$ and the quotient carries the measure `unipotentQuotientMeasure`. Second: the same assertion with the same constant $c$, for $\Theta^\vee(g) = \Theta({}^tg^{-1})$ in place of $\Theta$, expanded by a function $W'$ obeying the $\psi^{-1}$-Whittaker law and summing to $\Theta^\vee$, and paired with the Whittaker coefficient of $\varphi$ against $\psi$.
--
--   This is the unfolding step of the global $\mathrm{GL}_2 \times \mathrm{GL}_3$ Rankin–Selberg integral of Jacquet–Piatetski-Shapiro–Shalika, stated for an arbitrary pair $(\Theta, W)$ subject only to the mirabolic expansion, Whittaker transformation law, growth and half-plane convergence, rather than for a cubic induction form; the dual identity is recorded with the same constant. It is used in establishing the analytic continuation of the Rankin–Selberg integral and its identification, up to archimedean factors, with the $L$-function of the Rankin–Selberg datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual
    (Dp : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ c : ℂ, c ≠ 0 ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hWc : Continuous W) (_hWg : IsGaugeMajorised3 ℚ W)
        (_hWlaw : IsGL3PsiWhittakerFn ψ W)
        (_hWexp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W (mirabolicTranslate i * g)) (Θ g))
        (_hWhp : HasWhittakerHalfPlane W)
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          rsGlobalIntegral D s φ Θ =
            c * ∫ q, (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ⁻¹ φ 1 g *
                    W (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q)
              ∂(unipotentQuotientMeasure ℚ)) ∧
      (∀ (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (_hψ : IsGlobalAddChar ℚ ψ)
        (Θ W' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (_hΘc : Continuous Θ) (_hW'c : Continuous W') (_hW'g : IsGaugeMajorised3 ℚ W')
        (_hW'law : IsGL3PsiWhittakerFn ψ⁻¹ W')
        (_hW'exp : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, HasSum (fun i : MirabolicIndex ℚ => W' (mirabolicTranslate i * g)) (dualForm Θ g))
        (_hW'hp : HasWhittakerHalfPlane W')
        (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (_hφc : Continuous φ)
        (_hφ : ∀ (γ : GL (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
        (_hφb : ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ * detNorm g ^ (-(1 / 2 : ℝ)) ≤ C)
        (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
        (_hD : IsFundamentalDomain (globalPoints (𝓞 ℚ) ℚ).range D
          (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ))
        (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ)
        (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q),
        ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
          rsGlobalIntegral D s φ (dualForm Θ) =
            c * ∫ q, (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
                  whittakerCoefficient ℚ (productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)) ψ φ 1 g *
                    W' (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)) (σq q)
              ∂(unipotentQuotientMeasure ℚ)) := by sorry
