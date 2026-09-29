-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable
-- name    : LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/5ecbf969-d8ff-5f2b-b226-47bf5e9b3394
-- title:
--   Archimedean–finite splitting of the unipotent-quotient Rankin–Selberg integral
-- statement:
--   Work with $G = \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ carried by its Borel $\sigma$-algebra (assumed second countable) and with $\mathrm{GL}_2(\mathbb{R})$ carried by its Borel $\sigma$-algebra. Let $\mu_f$ be a Haar measure on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch` on $G$; let $\mu_{N,\infty}$ be a Haar measure on `realUnipotent`, the image of `unipotentGL2Hom` over $\mathbb{R}$, and $\mu_{N,f}$ a Haar measure on `finUnipotent`, the adelic unipotent subgroup `adelicUnipotent ℚ` regarded inside the finite-adelic subgroup. Write $g \mapsto (g_\infty, g_f)$ for the map sending $g$ to `ratArchGL2 g` (the archimedean component at the unique infinite place of $\mathbb{Q}$, transported to $\mathrm{GL}_2(\mathbb{R})$) and to `finFactor g` $= \bigl(\mathrm{archRealGLAt}(g_\infty)\bigr)^{-1} g$. Assume this map carries `adelicGLHaar` to the product of `archMeasure` (Lebesgue measure on $2\times 2$ real matrices pulled back and weighted by $|\det|^{-2}$) with $\mu_f$, and carries `unipotentHaar ℚ` to the product of the images of $\mu_{N,\infty}$ and $\mu_{N,f}$ under the inclusions into the ambient groups. Let $s \in \mathbb{C}$, let $W_\infty, F_\infty$ be complex functions on $\mathrm{GL}_2(\mathbb{R})$ and $W_f, F_f$ complex functions on the finite-adelic subgroup, and let $f \colon G \to \mathbb{C}$ satisfy $$f(g) = W_\infty(g_\infty) F_\infty(g_\infty)\,|\det g_\infty|^{s-1/2} \cdot W_f(g_f) F_f(g_f)\, \|\det g_f\|^{s-1/2},$$ the second norm being the idele norm of $\mathbb{Q}$ given by the distributive Haar character. Assume $f$ is measurable and left invariant under `adelicUnipotent ℚ`, let $\sigma$ be any section of the projection of $G$ onto the orbit quotient `UnipotentQuotient ℚ` by left multiplication by `adelicUnipotent ℚ`, and assume $q \mapsto f(\sigma q)$ is integrable for `unipotentQuotientMeasure ℚ`, the pushforward to the quotient of `adelicGLHaar` weighted by the quotient density attached to `unipotentHaar ℚ`. Then $\int_{q} f(\sigma q)$ against that quotient measure equals the product `rsArchIntegral archMeasure μNArch s WArch FArch` $\cdot$ `rsFinIntegral μf μNFin s Wf Ff`, the two local Rankin–Selberg integrals of $W \cdot F$ against $|\det|^{s-1/2}$, respectively $\|\det\|^{s-1/2}$, taken over the local groups with the local Haar measures weighted by the corresponding unipotent quotient densities.
--
--   This is the archimedean–finite factorisation of the unfolded global Rankin–Selberg zeta integral, with the integrability hypothesis placed on the quotient side rather than on the product of the two density-weighted local measures. It feeds the assembly of the global Rankin–Selberg integral as a product of local integrals with the $L$-function, used in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable.lean

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

theorem LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral_of_integrable

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
    ∫ q, f (σq q) ∂(unipotentQuotientMeasure ℚ) =
      rsArchIntegral archMeasure μNArch s WArch FArch * rsFinIntegral μf μNFin s Wf Ff := by sorry
