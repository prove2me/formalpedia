-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
-- name    : LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/cda7a9fd-7149-53d3-8e92-ced0bb39ba44
-- title:
--   Tonelli peel of the finite Rankin–Selberg lower integral
-- statement:
--   Fix a Haar measure $\mu$ on the group `finiteAdelicGL2Subgroup ℚ` of elements of $GL_2(\mathbb{A}_{\mathbb{Q}})$ killed by the archimedean projection, a Haar measure $\mu_N$ on its subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) cut out by the adelic unipotent subgroup, and assume the ambient group second countable. Let $S$ be a finite set of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, and for each $v$ let $\varpi_v$ lie in the valuation ring of $K_v$, with $\varpi_v\neq 0$ in $K_v$ and $v(\varpi_v)=\exp(-1)$ for $v\notin S$, i.e. a uniformiser. Let $\lambda,\omega,\lambda',\omega'$ be complex-valued functions on primes and $\kappa\in\mathbb{R}$, with all four bounded by $q_v^{\kappa}$ at $v\notin S$, where $q_v$ is the absolute norm of $v$. Let $W,F:GL_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ satisfy: the product $WF$ is invariant under left translation by [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); at each $v\notin S$ there is an additive character $\psi_v$ of $K_v$, trivial on the integers and non-trivial on $\varpi_v^{-1}$ times the integers, with $W(u_v(x)g)=\psi_v(x)W(g)$ for the upper unipotent $u_v(x)$ embedded at $v$; $W$ and $F$ are right invariant under [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $GL_2(K_v)$ whose image under the embedding at $v$ lies in the finite level subgroup of level the unit ideal; and the two-parameter torus law holds: for $v\notin S$, $g$ with trivial $v$-component and $m,n\in\mathbb{Z}$, the value of $WF$ at $g$ times the image at $v$ of $\mathrm{diag}(\varpi_v^{m},1)\cdot(\varpi_v I)^{n}$ equals $W(g)F(g)$ times $(\omega_v\omega'_v)^{n}$ multiplied by the two values at $m$ of the recursion `heckeRecursionSeq` with data $(q_v,\lambda_v,\omega_v)$ and $(q_v,\lambda'_v,\omega'_v)$, when $m,n\ge 0$, and zero otherwise. Assume $g\mapsto W(g)F(g)$ measurable, and let $\tau\in\mathbb{R}$. Then, for the measure $\mu$ weighted by the orbit density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $\mu_N$, the lower integral of $\|W(g)F(g)\|_e\cdot\mathrm{ofReal}(\|\det g\|^{\tau})$, with $\|\cdot\|$ the idèle norm given by the distributive Haar character, equals the product over $v\notin S$ of $\sum_{(p_1,p_2)\in\mathbb{Z}^2}\mathrm{ofReal}\bigl(q_v^{p_1-p_2}\,|c_v(p_1-p_2,p_2)|\,(q_v^{-(p_1+p_2)})^{\tau}\bigr)$, with $c_v$ the torus coefficient above, times the same lower integral with $W$ and $F$ each replaced by its indicator restriction to the set of $g$ whose component at every $v\notin S$ factors as an element of the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33) over $K_v$ times an element of that local level subgroup.
--
--   This is the Euler-factor (Tonelli) peel for the finite part of the Rankin–Selberg integral: the unramified torus law at the places outside $S$ converts the integral over the whole finite-adèlic group into an explicit product of local cell series times the integral over the big-cell locus. It feeds the integrability clause of the rational Rankin–Selberg package, [`LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_integrable_finWhittaker_rpow_ideleNorm_det_rat), and is obtained from the one-place version together with continuity of the idèle norm of the determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law.lean

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

theorem LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hN : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
      (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers ℚ,
        ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
      ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hWK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) *
        F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (W g * F g))
    (hm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (τ : ℝ) :
    ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
        ‖W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
      (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) *
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
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by sorry
