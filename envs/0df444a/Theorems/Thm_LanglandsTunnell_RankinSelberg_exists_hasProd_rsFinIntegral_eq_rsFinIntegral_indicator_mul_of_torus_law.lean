-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
-- name    : LanglandsTunnell.RankinSelberg.exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b5d7ade3-178d-50b0-85f3-7c55fcdf5ff1
-- title:
--   Peeling unramified Euler factors off the finite Rankin–Selberg integral
-- statement:
--   Fix a Haar measure $\mu$ on the group $\mathrm{finiteAdelicGL2Subgroup}\,\mathbb{Q}$ (the kernel of the archimedean component map on adelic $\mathrm{GL}_2$ over $\mathbb{Q}$, carrying the Borel structure coming from the adelic matrix algebra), a Haar measure $\mu_N$ on its subgroup $\mathrm{finUnipotent}$ cut out by the adelic unipotent subgroup, and assume the ambient group is second countable. Let $S$ be a finite set of height one primes of $\mathbb{Z}$, and for each $v$ let $\varpi_v$ lie in the valuation ring at $v$, required for $v\notin S$ to be nonzero in $\mathbb{Q}_v$ with $|\varpi_v|=\exp(-1)$, i.e. a uniformiser. Let $\lambda,\omega,\lambda',\omega'$ be complex-valued families on the primes and $\kappa$ real, with $\|\lambda_v\|,\|\omega_v\|,\|\lambda'_v\|,\|\omega'_v\|\le N(v)^{\kappa}$ for $v\notin S$, where $N(v)=\mathrm{absNorm}\,v$. Let $W,F$ be complex functions on adelic $\mathrm{GL}_2$ subject to: the product $WF$ is left invariant under $\mathrm{finUnipotent}$; for each $v\notin S$ there is an additive character $\psi$ of $\mathbb{Q}_v$, trivial on the integers and nontrivial on $\varpi_v^{-1}$ times the integers, with $W(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x)\cdot g)=\psi(x)W(g)$; both $W$ and $F$ are right invariant under $\mathrm{localLevelOne}\,v\,\top$ at each $v\notin S$, that is under the pullback along the local embedding at $v$ of the finite level-one subgroup of level $\top$; and the two-parameter torus law holds: for $v\notin S$, $g$ with trivial $v$-component and $m,n\in\mathbb{Z}$,
--   $$(WF)\bigl(g\cdot \mathrm{placeEmbed}\,v\,(\mathrm{diagZ}(\varpi_v,m)\cdot \mathrm{scalarPi}(\varpi_v)^{n})\bigr)=\mathbf 1[m\ge 0,\,n\ge 0]\,(\omega_v\omega'_v)^{n}\,u_m\,u'_m\,(WF)(g),$$
--   where $u_m=\mathrm{heckeRecursionSeq}\,N(v)\,\lambda_v\,\omega_v\,m$ and $u'_m$ is the same with $(\lambda'_v,\omega'_v)$, the sequence being given by $u_0=1$, $u_1=\lambda_v/N(v)$, $N(v)u_{m+2}=\lambda_v u_{m+1}-\omega_v u_m$. Then there exists $\sigma_0\in\mathbb{R}$ such that for every $s$ with $\sigma_0<\mathrm{Re}\,s$, provided $g\mapsto W(g)F(g)\,\|\det g\|^{\,s-1/2}$ (idele norm via the distributive Haar character) is integrable for $\mu$ weighted by the density $\mathrm{HaarQuotient.density}$ of $\mathrm{finUnipotent}$ with $\mu_N$, there is a complex number $\mathrm{Prod}$ which is the (unordered) product over the primes $v\notin S$ of $\bigl((\mathrm{rsEulerPoly}(\lambda_v/N(v),\omega_v/N(v),\lambda'_v/N(v),\omega'_v/N(v),0)\bigr)$ evaluated at $N(v)^{3/2-s}$, inverted, and such that $\mathrm{rsFinIntegral}\,\mu\,\mu_N\,s\,W\,F$ equals $\mathrm{Prod}$ times the same integral formed from $W$ and $F$ multiplied by the indicator of the set of $g$ whose component at each $v\notin S$ factors as a unipotent element times an element of $\mathrm{localLevelOne}\,v\,\top$.
--
--   This is the unramified computation in the $\mathrm{GL}_2\times\mathrm{GL}_2$ Rankin–Selberg convolution: away from a finite bad set the local integrals contribute the inverse of a degree-six Euler polynomial in $N(v)^{3/2-s}$, so that the finite-adelic zeta integral splits as a restricted integral over the cells at the good places times the partial Euler product. It feeds the global statement [`AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat`](thm.html#AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat), where the Rankin–Selberg integral against a Godement–Eisenstein series is compared with this Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law.lean

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

theorem LanglandsTunnell.RankinSelberg.exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law
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
         else 0) * (W g * F g)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable
        (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      ∃ Prod : ℂ,
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((rsEulerPoly (lam v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om v.1 / (Ideal.absNorm v.1.asIdeal : ℂ))
              (lam' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) (om' v.1 / (Ideal.absNorm v.1.asIdeal : ℂ)) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((3 / 2 : ℂ) - s)))⁻¹) Prod ∧
        RSCarrier.rsFinIntegral μ μN s (fun g => W g) (fun g => F g) =
          RSCarrier.rsFinIntegral μ μN s
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g))
              ({g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g)) *
            Prod := by sorry
