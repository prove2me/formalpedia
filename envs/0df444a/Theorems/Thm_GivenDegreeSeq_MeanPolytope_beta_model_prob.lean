-- Prove2me | Theorems.Thm_GivenDegreeSeq_MeanPolytope_beta_model_prob
-- name    : GivenDegreeSeq.MeanPolytope.beta_model_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:43:37.644432+00:00
-- url     : https://prove2.me/theorems/6123893d-b814-447b-818a-a9804d447dd5
-- title:
--   p. 6 — P_β is a probability measure and P_β(G) = e^{Σ β_i d_i} / ∏_{i<j}(1 + e^{β_i+β_j})
-- statement:
--   Let $\beta\in\mathbb R^n$ and let $\mathbb P_\beta$ be the law of the β-model on simple graphs with vertex set $\{1,\dots,n\}$: each pair $\{i,j\}$ is an edge independently with probability $p_{ij}=e^{\beta_i+\beta_j}/(1+e^{\beta_i+\beta_j})$.
--
--   Then $\mathbb P_\beta$ is a probability measure, and for every graph $G$ with degree sequence $d=(d_1,\dots,d_n)$,
--   $$\mathbb P_\beta(\{G\})=\frac{e^{\sum_i\beta_id_i}}{\prod_{i<j}\big(1+e^{\beta_i+\beta_j}\big)}.$$
--
--   The formula shows that the β-model is an exponential family on graphs whose sufficient statistic is the degree sequence. The proof of Theorem 1.4 uses it to show that $f_y\le 0$ on $\operatorname{conv}(\mathcal D)$.
--
--   **Formalization Note** The paper treats $\mathbb P_\beta$ as a law without comment; here the statement that it is a probability measure is an added conjunct. The probability is stated as an element of $[0,\infty]$, the real right-hand side being embedded by `ENNReal.ofReal`. The product runs over the pairs $i<j$ of `Fin n`.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6, §1.2 (formula after the definition of P_β); restated p. 16 in the proof of Theorem 1.4

import Mathlib
import Definitions.Def_GivenDegreeSeq_MeanPolytope_Model

namespace GivenDegreeSeq.MeanPolytope

open MeasureTheory

/-- Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, p. 6 (restated on p. 16): `P_β` is a probability
measure on graphs with vertex set `Fin n`, and the probability of a graph `G` with degree sequence
`d` is `e^{Σ_i β_i d_i} / ∏_{i<j} (1 + e^{β_i+β_j})`. -/
theorem beta_model_prob {n : ℕ} (β : Fin n → ℝ) :
    IsProbabilityMeasure (betaModel β) ∧
      ∀ G : SimpleGraph (Fin n),
        betaModel β {G} =
          ENNReal.ofReal
            (Real.exp (∑ i, β i * degSeq G i) /
              ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
                (1 + Real.exp (β i + β j))) := by sorry

end GivenDegreeSeq.MeanPolytope
