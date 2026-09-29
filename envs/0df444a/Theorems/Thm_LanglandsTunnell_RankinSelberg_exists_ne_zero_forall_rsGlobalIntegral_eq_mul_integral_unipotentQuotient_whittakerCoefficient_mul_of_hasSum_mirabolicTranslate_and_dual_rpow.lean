-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
-- name    : LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/ff983881-6619-5cc7-be4f-0440b8c14e30
-- title:
--   Unfolding the global GL₂timesGL₃ Rankin–Selberg integral, primal and dual
-- statement:
--   Let $Dp$ be a set in $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $U$ a family of subgroups of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ indexed by ideals of $\mathbb{Z}$ and $gen$ a family of elements indexed by the height-one spectrum; these enter only through the carrier data `productionPinsOf ℚ Dp U gen (AdelicBox.adelicBox ℚ)`, whose additive measure is the adelic additive Haar measure conditioned on the adelic box and whose group measure is `adelicGLHaar`. The assertion is that there is a constant $c\in\mathbb{C}$, $c\neq 0$, such that two statements hold simultaneously with this same $c$. First: for every additive character $\psi$ of $\mathbb{A}_{\mathbb{Q}}$ that is global (trivial on principal adeles, continuous, non-trivial), all $\Theta,W:\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ with $\Theta$ and $W$ continuous, $W$ gauge-majorised in the sense of `IsGaugeMajorised3` (vanishing off a prescribed root level and decaying there), $W$ satisfying $W(u(x,y,z)g)=\psi(x+y)W(g)$ for the upper unipotent $u(x,y,z)$ of $\mathrm{GL}_3$, the mirabolic expansion $\sum_{i} W(\iota(\gamma_i)g)=\Theta(g)$ as a convergent sum over $N_2(\mathbb{Q})\backslash\mathrm{GL}_2(\mathbb{Q})$ (with $\gamma_i$ the chosen coset representatives embedded by $\iota$), and $W$ having a Whittaker half-plane (finiteness of the corresponding $\|\det\|^{\sigma}$-weighted sum-integral over any fundamental domain for $\sigma$ large); and for every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ invariant under left translation by $\mathrm{GL}_2(\mathbb{Q})$ and satisfying $\|\varphi(g)\|\le C\,\|\det g\|^{r}$ for some $C,r\in\mathbb{R}$, every fundamental domain $D$ for $\mathrm{GL}_2(\mathbb{Q})$ in $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ for `adelicGLHaar`, and every section $\sigma q$ of the quotient map onto the quotient by the adelic unipotent subgroup, there is $\sigma_0\in\mathbb{R}$ with $$\int_D \varphi(g)\,\Theta(\iota g)\,\|\det g\|^{s-1/2}\,dg = c\int \big(W^{\psi^{-1}}_{\varphi}(\sigma q(q))\,W(\iota(\sigma q(q)))\,\|\det \sigma q(q)\|^{s-1/2}\big)\,d\mu(q)$$ for all $s$ with $\operatorname{Re} s>\sigma_0$, where $\mu$ is `unipotentQuotientMeasure` and $W^{\psi^{-1}}_{\varphi}(g)=\int \varphi(u(x)g)\,\psi^{-1}(-x)\,d\nu(x)$ is the Whittaker coefficient at $\alpha=1$ taken against the conditioned adelic measure $\nu$. Second: the same identity with $W$ replaced by a function $W'$ subject to the same continuity, gauge-majorisation and half-plane hypotheses but satisfying the $\psi^{-1}$-Whittaker law and expanding mirabolically to $\Theta^{\vee}(g)=\Theta({}^{t}g^{-1})$, with $\Theta$ replaced by $\Theta^{\vee}$ on the left and the Whittaker coefficient taken with respect to $\psi$ on the right.
--
--   This is the unfolding step of the global Rankin–Selberg integral for $\mathrm{GL}_2\times\mathrm{GL}_3$ in the form of Jacquet–Piatetski-Shapiro–Shalika, stated simultaneously for a $\mathrm{GL}_3$ function and its dual with one common normalisation constant, and with the growth condition on the $\mathrm{GL}_2$ form relaxed to a polynomial bound in $\|\det\|$. It is used in the Langlands–Tunnell part of the argument to factor the global integral into archimedean and finite contributions and to compare the integral against twisted realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_ne_zero_forall_rsGlobalIntegral_eq_mul_integral_unipotentQuotient_whittakerCoefficient_mul_of_hasSum_mirabolicTranslate_and_dual_rpow
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
        (_hφb : ∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r)
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
        (_hφb : ∃ C r : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖φ g‖ ≤ C * detNorm g ^ r)
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
