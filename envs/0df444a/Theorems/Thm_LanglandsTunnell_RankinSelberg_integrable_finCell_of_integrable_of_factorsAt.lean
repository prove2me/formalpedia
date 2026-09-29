-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt
-- name    : LanglandsTunnell.RankinSelberg.integrable_finCell_of_integrable_of_factorsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/6ae8d201-ec91-5b7e-8d5e-ca517ffd4986
-- title:
--   Integrability transfer at one place for Rankin–Selberg cell integrals
-- statement:
--   Fix a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, a Haar measure $\mu$ on the finite-adelic subgroup $\ker(\mathrm{glArch})\le \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and a Haar measure $\mu_N$ on [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), the adelic unipotent subgroup viewed inside that finite-adelic subgroup; assume $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ second countable. Let $W,F,W_0,F_0,W',F'$ be complex functions on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and $w,f,w_0,f_0$ complex functions on $\mathrm{GL}_2(\mathbb{Q}_p)$, with $W(g)=w(g_p)W'(g)$, $W_0(g)=w_0(g_p)W'(g)$, $F(g)=f(g_p)F'(g)$, $F_0(g)=f_0(g_p)F'(g)$, where $g_p$ is the component of $g$ at $p$; assume $W'$ and $F'$ are invariant under right multiplication by $\mathrm{GL}_2(\mathbb{Q}_p)$ embedded at $p$, that $|W'F'|$ is left invariant under [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43), that $|wf|$ and $|w_0f_0|$ are left invariant under the matrices $\binom{1\ x}{0\ 1}$, $x\in\mathbb{Q}_p$, and that $W'F'$ and $WF$ are measurable on the finite-adelic group. Let $s\in\mathbb{C}$. Then, for the Borel structure on $\mathrm{GL}_2(\mathbb{Q}_p)$, for every Haar measure $\mu_2$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ and every Haar measure $\mu_{N,2}$ on the image of $x\mapsto\binom{1\ x}{0\ 1}$, given measurability of $wf$ and $w_0f_0$: if $g\mapsto W_0(g)F_0(g)\,\|\det g\|^{s-1/2}$ (idele norm via `distribHaarChar`) is integrable for $\mu$ weighted by the quotient density of [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) relative to $\mu_N$, if the lower integral of $\|(w_0f_0)(y)\,\mathrm{modulus}(\det y)^{s-1/2}\|$ against $\mu_2$ weighted by the corresponding local unipotent density is non-zero, and if the same integral with $(w,f)$ in place of $(w_0,f_0)$ is finite, then $g\mapsto W(g)F(g)\,\|\det g\|^{s-1/2}$ is integrable for the weighted measure on the finite-adelic group.
--
--   This is the integrability half of the one-place factorisation of finite-adelic Rankin–Selberg integrals: with the prime-to-$p$ data $W',F'$ frozen, absolute convergence is moved from one local test pair at $p$ to another whose local integral converges absolutely and whose reference integral is non-zero. It is used in the construction of integrable cell integrands for the Rankin–Selberg convolution, in particular by [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge) and by [`LanglandsTunnell.RankinSelberg.integrable_pureTensorTerm_dual_and_hybrid_of_integrable_cutoff_of_forall_lintegral_lt_top`](thm.html#LanglandsTunnell.RankinSelberg.integrable_pureTensorTerm_dual_and_hybrid_of_integrable_cutoff_of_forall_lintegral_lt_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
open scoped ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.integrable_finCell_of_integrable_of_factorsAt
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (W F W₀ F₀ W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (w f w₀ f₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = w (localAt ℚ p g) * W' g)
    (hW₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W₀ g = w₀ (localAt ℚ p g) * W' g)
    (hF : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = f (localAt ℚ p g) * F' g)
    (hF₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F₀ g = f₀ (localAt ℚ p g) * F' g)
    (hW' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ p x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ p x) = F' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖)
    (hn : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w (unipotent x * g) * f (unipotent x * g)‖ = ‖w g * f g‖)
    (hn₀ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w₀ (unipotent x * g) * f₀ (unipotent x * g)‖ = ‖w₀ g * f₀ g‖)
    (hWFm' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g * F' g)
    (hWFm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      Measurable (fun y => w y * f y) → Measurable (fun y => w₀ y * f₀ y) →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W₀ g * F₀ g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w₀ y * f₀ y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ≠ 0 →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w y * f y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) < ⊤ →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by sorry
