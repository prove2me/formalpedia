-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support
-- name    : LanglandsTunnell.RankinSelberg.lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ffbcda7d-3f28-5c77-a7ee-d2779eecdcb1
-- title:
--   Finiteness of a big-cell integral against ‖det‖^τ
-- statement:
--   Work in $G=$ `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean component map on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, and let $N=$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) be the subgroup of $G$ cut out by the image of $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ on $\mathbb A_{\mathbb Q}$. Given a Haar measure $\mu$ on $G$, a Haar measure $\mu_N$ on $N$, a second-countability assumption on $G$, a finite set $S$ of height-one primes of $\mathbb Z$, functions $W,F\colon \mathrm{GL}_2(\mathbb A_{\mathbb Q})\to\mathbb C$ such that $g\mapsto W(g)F(g)$ is measurable on $G$ and satisfies $W(ng)F(ng)=W(g)F(g)$ for all $n\in N$, $g\in G$, and a real $\tau$, assume further: there are a compact $\mathrm{Cpt}\subseteq G$ and a real $B_0$ with $\|W(g)F(g)\|\le B_0$ for all $g\in G$, such that every $g\in G$ lying in the big cell $\mathcal C_S$ — those $g$ whose component `localAt ℚ v g` factors as $n\,k$ with $n$ unipotent upper triangular over $\mathbb Q_v$ and $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (the preimage under the local embedding at $v$ of the finite level-one subgroup at the unit ideal), for every $v\notin S$ — and with $W(g)F(g)\ne 0$ admits $n\in N$ and $h\in\mathrm{Cpt}$ with `localAt ℚ v (n*g) = localAt ℚ v h` for all $v\in S$. Then the lower integral over $G$ of $\|\mathbf 1_{\mathcal C_S}W(g)\cdot\mathbf 1_{\mathcal C_S}F(g)\|_{e}\cdot\mathrm{ofReal}\big(\|\det g\|_{\mathbb A}^{\tau}\big)$, the norm being `TateGlobal.ideleNorm` and the measure being $\mu$ weighted by [`HaarQuotient.density RSCarrier.finUnipotent μN`](def/HaarQuotient.html#L25), is finite.
--
--   This is the finiteness half of the convergence estimate for a finite-adelic Rankin–Selberg integrand on $N\backslash \mathrm{GL}_2(\mathbb A_{\mathbb Q,f})$: boundedness together with compact support modulo $N$ at the places of $S$ and level-one behaviour away from $S$ forces the $\|\det\|^{\tau}$-twisted integral to converge. It is used by [`AutomorphicForm.integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat`](thm.html#AutomorphicForm.integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat) and by the Rankin–Selberg package [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support.lean

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

theorem LanglandsTunnell.RankinSelberg.lintegral_indicator_bigCell_enorm_mul_rpow_ideleNorm_det_lt_top_of_support
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hsupp : ∃ (Cpt : Set (finiteAdelicGL2Subgroup ℚ)) (B₀ : ℝ), IsCompact Cpt ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ, ‖W g * F g‖ ≤ B₀) ∧
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
            ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
        W g * F g ≠ 0 →
          ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
            ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
              localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ))
    (τ : ℝ) :
    ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
        ‖{g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g) g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g) g‖ₑ *
          ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) < ⊤ := by sorry
