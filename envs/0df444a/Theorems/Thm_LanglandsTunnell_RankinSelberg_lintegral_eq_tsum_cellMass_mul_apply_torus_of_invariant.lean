-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant
-- name    : LanglandsTunnell.RankinSelberg.lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/ee6c0fc5-e7e5-5eb6-8770-dea76584b0e8
-- title:
--   Iwasawa cell series for an N-K-invariant local integral
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal O_{\mathbb Q}$, write $\mathbb Q_v$ for the $v$-adic completion and $G=\mathrm{GL}_2(\mathbb Q_v)$, taken second countable and equipped with its Borel $\sigma$-algebra, and let $q$ be `Ideal.absNorm v.asIdeal`. Let $\varpi$ lie in the valuation ring of $v$ with nonzero image $\pi$ in $\mathbb Q_v$ and $\mathrm{v}(\pi)=\exp(-1)$, so $\pi$ is a uniformiser. Let $N$ be the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33), i.e. the subgroup of matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb Q_v$. Then for every Haar measure $\mu$ on $G$, every Haar and right-invariant measure $\mu_N$ on $N$, and every $f\colon G\to[0,\infty]$ with $f(ng)=f(g)$ for all $n\in N$, $g\in G$, and $f(gk)=f(g)$ for all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) (those $g$ whose image under [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) into $\mathrm{GL}_2$ of the finite adèles lies in `AdelicLevel.finiteLevelOne` at the ideal $\top$, that is, both that image matrix and its inverse satisfy `IsLevelOneMatrix` for $\top$), one has, with $\nu=\mu$ weighted by the coset density [`HaarQuotient.density`](def/HaarQuotient.html#L25) of $N$, namely $\rho(g)=w(g)/\int_N w(xg)\,d\mu_N(x)$ for the compact-exhaustion weight $w=$ [`HaarQuotient.weight`](def/HaarQuotient.html#L12),
--   $$\int^{-}_G f\,d\nu=\sum_{(p_1,p_2)\in\mathbb Z\times\mathbb Z}\nu(N\!\cdot\!K)\,q^{\,p_1-p_2}\,f\bigl(\mathrm{diag}(\pi^{p_1-p_2},1)\,\mathrm{diag}(\pi,\pi)^{p_2}\bigr),$$
--   where $N\!\cdot\!K$ is the set of products $nk$ with $n\in N$ and $k$ in that level subgroup, and the torus element is `diagZ` at $p_1-p_2$ times the $p_2$-th power of `scalarPi`. No measurability or finiteness of $f$ is assumed; the identity holds in $[0,\infty]$.
--
--   This is the $[0,\infty]$-valued (Tonelli) form of the Iwasawa cell decomposition of an unramified local integral: $G$ decomposes into the cells $N\,\mathrm{diag}(\pi^{p_1},\pi^{p_2})\,K$, each of $\nu$-mass $q^{p_1-p_2}\nu(NK)$, and a function invariant under $N$ on the left and under the level-one subgroup on the right is constant on each cell. It supplies the local step in the evaluation of the finite Rankin–Selberg integral as a series over diagonal torus elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant.lean

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain UnramifiedWhittaker
open scoped ENNReal

theorem LanglandsTunnell.RankinSelberg.lintegral_eq_tsum_cellMass_mul_apply_torus_of_invariant
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (f : GL (Fin 2) (v.adicCompletion ℚ) → ℝ≥0∞)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (n * g) = f g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), f (g * k) = f g),
      ∫⁻ g, f g ∂(μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN)) =
        ∑' p : ℤ × ℤ,
          (μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k} *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (p.1 - p.2) *
            f (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) := by sorry
