-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable
-- name    : LanglandsTunnell.Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/89738af3-a123-507d-887b-9f4df7a1690d
-- title:
--   Finite Rankin–Selberg integrand integrable, or archimedean integral vanishes
-- statement:
--   Work with $G=\mathrm{GL}_2(\mathbb{A}_{\mathbb Q})$, assumed second countable and carrying its Borel structure, and with $\mathrm{GL}_2(\mathbb R)$ given the Borel $\sigma$-algebra. Fix Haar measures: $\mu_f$ on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean-component homomorphism `glArch`; $\mu_{N,\infty}$ on `realUnipotent`, the image of the one-parameter upper unipotent homomorphism over $\mathbb R$; and $\mu_{N,f}$ on `finUnipotent`, the adelic unipotent subgroup seen inside the finite-adelic subgroup. Assume two splitting hypotheses for the component map $g\mapsto(g_\infty,g_f)$, where $g_\infty$ is `ratArchGL2 g` (the component at the infinite place of $\mathbb Q$, transported to $\mathrm{GL}_2(\mathbb R)$) and $g_f$ is `finFactor g` $=\,$`archRealGLAt`$(g_\infty)^{-1}g$: the pushforward of `adelicGLHaar` is `archMeasure`$\times\mu_f$, with `archMeasure` the comap of Lebesgue measure on $2\times2$ real matrices weighted by $|\det|^{-2}$; and the pushforward of `unipotentHaar ℚ` is the product of the pushforwards of $\mu_{N,\infty}$ and $\mu_{N,f}$ into the ambient groups. Let $s\in\mathbb C$, $W_\infty,F_\infty$ on $\mathrm{GL}_2(\mathbb R)$, $W_f,F_f$ on the finite-adelic subgroup, and let $f:G\to\mathbb C$ be measurable, left invariant under the adelic unipotent subgroup, and equal to the pure tensor $W_\infty(g_\infty)F_\infty(g_\infty)|\det g_\infty|^{s-1/2}\cdot W_f(g_f)F_f(g_f)\|\det g_f\|^{s-1/2}$, the finite factor using the idele norm. Let $\sigma$ be any set-theoretic section of the quotient map onto the orbit quotient `UnipotentQuotient ℚ`, and assume $f\circ\sigma$ is integrable for `unipotentQuotientMeasure ℚ`. Then either $k\mapsto W_f(k)F_f(k)\|\det k\|^{s-1/2}$ is integrable for $\mu_f$ weighted by the density [`HaarQuotient.density finUnipotent`](def/HaarQuotient.html#L25)$\,\mu_{N,f}$, or `rsArchIntegral archMeasure` $\mu_{N,\infty}\,s\,W_\infty\,F_\infty=0$.
--
--   This is the dichotomy accompanying the archimedean–finite factorisation of the unfolded global Rankin–Selberg integral for $\mathrm{GL}_2$ over $\mathbb Q$: integrability of the unfolded integrand on the unipotent quotient forces either integrability of the finite local integrand against the density-weighted finite Haar measure or vanishing of the archimedean local integral. It is used in the assembly of the global zeta integral as a product of local integrals and in the associated dual identity for families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm LanglandsTunnell RSCarrier

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option autoImplicit false

theorem LanglandsTunnell.Converse.integrable_rsFinIntegrand_or_rsArchIntegral_eq_zero_of_integrable

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :

    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀

    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
    (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure]

    (_hsplit : Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf)

    (_hNsplit : Measure.map
        (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
        (unipotentHaar ℚ) =
        (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin))

    (s : ℂ)
    (WArch FArch : GL (Fin 2) ℝ → ℂ) (Wf Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
    (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (_hf : ∀ g, f g =
      ((WArch (ratArchGL2 g) * FArch (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
        ((Wf (finFactor g) * Ff (finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
              (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))))

    (_hfm : Measurable f)
    (_hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), f ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = f g)
    (σq : UnipotentQuotient ℚ → AdelicGL2 (𝓞 ℚ) ℚ) (_hσq : ∀ q, (Quotient.mk'' (σq q) : UnipotentQuotient ℚ) = q)

    (_hIq : Integrable (fun q : UnipotentQuotient ℚ => f (σq q)) (unipotentQuotientMeasure ℚ)),
    Integrable (fun k : finiteAdelicGL2Subgroup ℚ =>
        (Wf k * Ff k) *
          ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (k : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) ∨
      rsArchIntegral archMeasure μNArch s WArch FArch = 0 := by sorry
