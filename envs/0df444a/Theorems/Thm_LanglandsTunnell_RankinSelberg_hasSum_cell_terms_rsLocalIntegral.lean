-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral
-- name    : LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/5c30375b-3ebb-5782-bf39-626259c93039
-- title:
--   Cell expansion of the local Rankin–Selberg integral
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb{Q}}$, write $G = \mathrm{GL}_2(\mathbb{Q}_v)$ for the general linear group over the completion of $\mathbb{Q}$ at $v$, assumed second countable and equipped with its Borel $\sigma$-algebra, and let $\varpi$ be an element of the valuation ring whose image $\pi$ in $\mathbb{Q}_v$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Let $N \le G$ be the range of [`AutomorphicForm.unipotentGL2Hom`](def/AutomorphicForm_ConstantTerm.html#L33), the homomorphism sending $x$ to $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and let $K =$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178) be the preimage under the local embedding $G \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the level-one subgroup at the unit ideal, i.e. of the matrices that together with their inverses satisfy `IsLevelOneMatrix` for $N = \top$. Fix a Haar measure $\mu$ on $G$, a Haar measure $\mu_N$ on $N$ that is also right invariant, a function $\delta : G \to \mathbb{R}$ with $\delta(ng) = \delta(g)$ for $n \in N$ and $\delta(gk) = \delta(g)$ for $k \in K$, a complex number $s$, and functions $W, F : G \to \mathbb{C}$ whose product satisfies $W(ng)F(ng) = W(g)F(g)$ for $n \in N$ and $W(gk)F(gk) = W(g)F(g)$ for $k \in K$. Write $\nu = \mu$ weighted by the density [`HaarQuotient.density`](def/HaarQuotient.html#L25) for $N$ and $\mu_N$ (at $g$, the value of the Haar-quotient weight at $g$ divided by the $\mu_N$-integral of $x \mapsto$ weight$(xg)$), and assume $g \mapsto W(g)F(g)\,\delta(g)^{s-1/2}$ is $\nu$-integrable. Then the family indexed by pairs $(m_1,m_2) \in \mathbb{Z} \times \mathbb{Z}$ whose term is $\nu(NK)$, where $NK = \{g : g = nk,\ n \in N,\ k \in K\}$, times $(\#(\mathcal{O}_{\mathbb{Q}}/v))^{m_1-m_2}$, times $W(g)F(g)\,\delta(g)^{s-1/2}$ evaluated at $g = \mathrm{diag}(\pi^{m_1-m_2},1)\cdot(\pi I)^{m_2}$, is summable with sum [`RSCarrier.rsLocalIntegral`](def/LanglandsTunnell_RSCarrier.html#L16) $\mu\, N\, \mu_N\, \delta\, s\, W\, F$, that is, the $\nu$-integral of $W F \delta^{s-1/2}$.
--
--   This is the reduction of the local Rankin–Selberg integral at a finite place to a double series over the exponents of the diagonal torus, obtained by decomposing $G$ into the cells $N \,\mathrm{diag}(\pi^{m_1},\pi^{m_2})\, K$ and using the left $N$- and right $K$-invariance of the integrand. It is the computational input to the cubic-induction steps of the Langlands–Tunnell argument, which use it to identify local Rankin–Selberg integrals with polynomial expressions in the torus values of Whittaker functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_hasSum_cell_terms_rsLocalIntegral.lean

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

theorem LanglandsTunnell.RankinSelberg.hasSum_cell_terms_rsLocalIntegral
    (v : HeightOneSpectrum (𝓞 ℚ)) [SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ))]
    {ϖ : v.adicCompletionIntegers ℚ}
    (hπ : algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borel (GL (Fin 2) (v.adicCompletion ℚ))
    ∀ (μ : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μ.IsHaarMeasure]
      (μN : Measure (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μN.IsHaarMeasure]
      [μN.IsMulRightInvariant]
      (δ : GL (Fin 2) (v.adicCompletion ℚ) → ℝ)
      (_hδN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (n * g) = δ g)
      (_hδK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), δ (g * k) = δ g)
      (s : ℂ) (W F : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
      (_hN : ∀ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (n * g) * F (n * g) = W g * F g)
      (_hK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
        ∀ g : GL (Fin 2) (v.adicCompletion ℚ), W (g * k) * F (g * k) = W g * F g)
      (_hint : Integrable
        (fun g : GL (Fin 2) (v.adicCompletion ℚ) => (W g * F g) * ((δ g : ℝ) : ℂ) ^ (s - 1 / 2))
        (μ.withDensity
          (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))),
      HasSum (fun p : ℤ × ℤ =>
          (((μ.withDensity
                (HaarQuotient.density (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN))
              {g : GL (Fin 2) (v.adicCompletion ℚ) |
                ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                  ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, g = n * k}).toReal : ℂ) *
            ((Ideal.absNorm v.asIdeal : ℂ) ^ (p.1 - p.2)) *
            ((W (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) *
                F (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2)) *
              ((δ (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ (p.1 - p.2) *
                  scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) ϖ) hπ ^ p.2) :
                    ℝ) : ℂ) ^ (s - 1 / 2)))
        (RSCarrier.rsLocalIntegral μ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN δ s W
          F) := by sorry
