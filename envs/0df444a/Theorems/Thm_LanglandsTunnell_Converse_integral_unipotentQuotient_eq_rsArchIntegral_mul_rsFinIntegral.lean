-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral
-- name    : LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/231b1035-109b-5f09-aee6-6a99eff8aac4
-- title:
--   Factorisation of the unipotent-quotient integral into archimedean and finite Rankin–Selberg factors
-- statement:
--   Work over $\mathbb{Q}$ with the Borel $\sigma$-algebras on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ and on $\mathrm{GL}_2(\mathbb{R})$, and assume $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ second countable. Fix Haar measures $\mu_f$ on `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection `glArch`), $\mu_{N,\infty}$ on `realUnipotent` (the image of `unipotentGL2Hom` over $\mathbb{R}$) and $\mu_{N,f}$ on `finUnipotent` (the adelic unipotent subgroup viewed inside the finite subgroup). Assume two splitting hypotheses for the map $g \mapsto (\mathtt{ratArchGL2}\,g, \mathtt{finFactor}\,g)$, namely that it pushes `adelicGLHaar` forward to `archMeasure` (Lebesgue measure on the matrix entries with density $|\det|^{-2}$) times $\mu_f$, and pushes `unipotentHaar` (additive adelic Haar measure transported by `unipotentGL2Hom`, normalised on the adelic box) forward to the product of the images of $\mu_{N,\infty}$ and $\mu_{N,f}$ under the inclusions. Fix $s \in \mathbb{C}$, functions $W_\infty, F_\infty$ on $\mathrm{GL}_2(\mathbb{R})$ and $W_f, F_f$ on the finite subgroup, and a measurable $f$ on $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ equal at every $g$ to $W_\infty F_\infty(\mathtt{ratArchGL2}\,g)\,|\det|^{s-1/2}$ times $W_f F_f(\mathtt{finFactor}\,g)$ times the $(s-1/2)$-power of the idele norm of the determinant of the finite factor; assume $f$ invariant under left multiplication by `adelicUnipotent ℚ`, a section $\sigma$ of the quotient map onto `UnipotentQuotient ℚ`, and integrability of the corresponding product integrand against the product of `archMeasure` and $\mu_f$ weighted by the densities [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $\mu_{N,\infty}$ and $\mu_{N,f}$. Then $\int f(\sigma q)$ against `unipotentQuotientMeasure ℚ` equals `rsArchIntegral archMeasure μNArch s WArch FArch` times `rsFinIntegral μf μNFin s Wf Ff`.
--
--   This is the global-to-local factorisation step for the Rankin–Selberg integral of a Whittaker-type function over the unipotent quotient of $\mathrm{GL}_2$ over $\mathbb{Q}$: under the assumed splittings of the two Haar measures, the quotient integral becomes the product of the archimedean and finite Rankin–Selberg carrier integrals. It is used by [`LanglandsTunnell.RankinSelberg.rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul`](thm.html#LanglandsTunnell.RankinSelberg.rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral.lean

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

theorem LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral

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

    (_hint : Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
        ((WArch p.1 * FArch p.1) * (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
          ((Wf p.2 * Ff p.2) *
            ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
              ^ (s - 1 / 2))))
      ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin)))),
    ∫ q, f (σq q) ∂(unipotentQuotientMeasure ℚ) =
      rsArchIntegral archMeasure μNArch s WArch FArch * rsFinIntegral μf μNFin s Wf Ff := by sorry
