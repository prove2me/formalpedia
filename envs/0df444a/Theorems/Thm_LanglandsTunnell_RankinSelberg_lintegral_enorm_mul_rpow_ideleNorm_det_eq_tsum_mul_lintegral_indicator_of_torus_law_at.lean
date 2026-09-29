-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at
-- name    : LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/2e31d7b9-9b11-5d7c-a8c1-49eaba97288b
-- title:
--   One-place torus peel for a Rankin–Selberg lower integral
-- statement:
--   Let $\mu$ be a Haar measure on the group $\mathrm{finiteAdelicGL2Subgroup}\ \mathbb{Q}$ of elements of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ with trivial archimedean component (the kernel of `AdelicLevel.glArch`), assumed second countable, and let $\mu_N$ be a Haar measure on the subgroup $N$ of that group cut out by the image of `unipotentGL2Hom` over $\mathbb{A}_{\mathbb{Q}}$, i.e. the adelic upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Let $v$ be a nonzero prime of $\mathbb{Z}$ and $\varpi$ an element of the valuation ring at $v$ whose image $\pi$ in $\mathbb{Q}_v$ is nonzero of valuation $\exp(-1)$, i.e. a uniformiser. Let $c:\mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$ be a table of coefficients and $W,F:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ functions such that: (i) $g\mapsto W(g)F(g)$ is invariant under left translation by $N$; (ii) both $W$ and $F$ are invariant under right translation by $\mathrm{placeEmbed}_v(x)$ for every $x$ in $K_v=\mathrm{AdelicDock.localLevelOne}\ (\mathcal{O}_{\mathbb{Q}})\ \mathbb{Q}\ v\ \top$, the preimage under `localEmbed` at $v$ of the finite level-one group of the unit ideal; (iii) the torus law $W(g\,\iota_v(t_{m,n}))F(g\,\iota_v(t_{m,n})) = c(m,n)\,W(g)F(g)$ holds for all $m,n\in\mathbb{Z}$ and all $g$ with trivial $v$-component, where $\iota_v=\mathrm{placeEmbed}_v$ and $t_{m,n}=\mathrm{diag}(\pi^m,1)\cdot(\pi I)^n$; and (iv) $g\mapsto W(g)F(g)$ is measurable on the finite-adelic subgroup. Then for every real $\tau$, writing $q=|\mathbb{Z}/v|$ and integrating against $\mu$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$ with respect to $\mu_N$, the $[0,\infty]$-valued lower integral of $\|W(g)F(g)\|\cdot\|\det g\|_{\mathbb{A}}^{\tau}$ equals $$\Bigl(\sum_{(p_1,p_2)\in\mathbb{Z}^2} q^{\,p_1-p_2}\,|c(p_1-p_2,p_2)|\,\bigl(q^{-(p_1+p_2)}\bigr)^{\tau}\Bigr)$$ times the same lower integral with $W$ and $F$ each replaced by its restriction (indicator) to the set of $g$ whose $v$-component `localAt ℚ v g` lies in the big cell $N_v\cdot K_v$, $N_v$ being the image of `unipotentGL2Hom` over $\mathbb{Q}_v$. No integrability is assumed; both sides may be infinite.
--
--   This is the local unfolding step at a single place in the Rankin–Selberg computation: the Iwasawa-type decomposition of $\mathrm{GL}_2(\mathbb{Q}_v)$ into unipotent times torus times maximal compact converts a torus multiplicativity law for $W\cdot F$ into a scalar factor, here as an identity of lower Lebesgue integrals in $[0,\infty]$ rather than of Bochner integrals. It is cited by [`LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law`](thm.html#LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law), which iterates it over the places and passes to the product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (v : HeightOneSpectrum (𝓞 ℚ)) {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    (c : ℤ → ℤ → ℂ) (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hWK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hT : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) *
        F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ n)) =
        c m n * (W g * F g))
    (hm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (τ : ℝ) :
    ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
        ‖W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
      (∑' p : ℤ × ℤ,
          ENNReal.ofReal
            (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) * ‖c (p.1 - p.2) p.2‖ *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) *
        ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
          ‖{g : finiteAdelicGL2Subgroup ℚ |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g) g *
              {g : finiteAdelicGL2Subgroup ℚ |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g) g‖ₑ *
            ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by sorry
