-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/61fcd53f-0c20-565d-babe-cdd04cf618d5
-- title:
--   Convergence of finite-adelic big-cell Rankin–Selberg integrals under a gauge bound
-- statement:
--   Let $SQ \subseteq S'$ be finite sets of height-one primes of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$. For each prime $v$ let $L_v \colon \mathrm{GL}_3(\mathbb{Q}_v) \to \mathbb{C}$ be locally constant and satisfy $\|L_v(\iota(n(x))h)\| = \|L_v(h)\|$ for all $x \in \mathbb{Q}_v$ and $h$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\iota =$ `iotaGL` is the embedding $\mathrm{GL}_2 \to \mathrm{GL}_3$, $g \mapsto \mathrm{diag}(g,1)$; for $v \notin S'$ assume $L_v(\iota(k)) = 1$ for every $k$ in the local level-one subgroup at $v$ (the pullback along the local embedding of the finite level-one group of the unit ideal); and for $v \in S'$ assume there are $B$, $t \in \mathbb{N}$, $C$ with, writing $\rho_1(h) = \mathrm{detSize}(h)\cdot\mathrm{lastRowSup}(h)/\mathrm{minorSup}(h)^2$ and $\rho_2(h) = \mathrm{minorSup}(h)/\mathrm{lastRowSup}(h)^2$ (here $\mathrm{detSize}(h) = \|\det h\|$, $\mathrm{lastRowSup}$ the maximum of the norms of the three entries of the bottom row, $\mathrm{minorSup}$ the maximum of the norms of the three $2\times 2$ minors of the bottom two rows), that $L_v(h) = 0$ unless $\rho_1(h) \le B$ and $\rho_2(h) \le B$, and $\|L_v(h)\| \le C/(\rho_1(h)\rho_2(h))^t$ on that region. Let $B \colon \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})^{\mathrm{arch}=1} \to \mathbb{C}$ (the kernel of the archimedean component map) be measurable with $\|B(g)\| \le M\,\|\det g\|^{r}$ for some real $M, r$, where $\|\cdot\|$ is the idèle norm given by the Haar character module. Let $\mu_f$ be a Haar measure on this finite-adelic group and $\mu_N$ a Haar measure on the adelic upper unipotent subgroup inside it. Then there exists $\sigma \in \mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s > \sigma$ the function $g \mapsto \mathbf{1}_{\mathcal{C}}(g)B(g) \cdot \mathbf{1}_{\mathcal{C}}(g)\prod^{\mathrm{f}}_{v} L_v(\iota(g_v)) \cdot \|\det g\|^{s - 1/2}$ is integrable for $\mu_f$ weighted by the density attached to the unipotent subgroup and $\mu_N$, where $\mathcal{C}$ is the set of $g$ whose component at each prime $p \notin SQ$ factors as $g_p = nk$ with $n$ in the range of the unipotent homomorphism and $k$ in the local level-one subgroup at $p$ of the unit ideal.
--
--   This is the absolute convergence statement for the finite-adelic big-cell Rankin–Selberg integral of a gauge-majorised Euler-factorisable $\mathrm{GL}_3$ datum against a $\mathrm{GL}_2$ weight of polynomial determinant growth. It is used to establish integrability of the cell integrands built from the local Whittaker functions of a cubic induction datum and their duals, in [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_rsFinCellIntegrand_translate_and_dual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction
  MeasureTheory NumberField.TateGlobal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem LanglandsTunnell.RankinSelberg.exists_forall_integrable_bigCell_indicator_mul_finprod_iotaGL_of_gauge
    (SQ S' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSS' : SQ ⊆ S')

    (L : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ)
    (hLlc : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsLocallyConstant (L v))
    (hLphase : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) (h : LocalGL3 v),
      ‖L v (iotaGL (unipotentGL2 x) * h)‖ = ‖L v h‖)
    (hLone : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S' →
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, L v (iotaGL k) = 1)
    (hLgauge : ∀ v ∈ S', ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → L v h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖L v h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t))

    (B : finiteAdelicGL2Subgroup ℚ → ℂ) (hBm : Measurable B)
    (hBgr : ∃ M r : ℝ, ∀ g : finiteAdelicGL2Subgroup ℚ,
      ‖B g‖ ≤ M * ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ r)

    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
    (μNFin : Measure RSCarrier.finUnipotent) [μNFin.IsHaarMeasure] :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ =>
          {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator B g *
            {g : finiteAdelicGL2Subgroup ℚ | ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
              ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := p.adicCompletion ℚ)).range,
                ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
                  localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
              L v (iotaGL (localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ)))) g *
            ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μf.withDensity (HaarQuotient.density RSCarrier.finUnipotent μNFin)) := by sorry
