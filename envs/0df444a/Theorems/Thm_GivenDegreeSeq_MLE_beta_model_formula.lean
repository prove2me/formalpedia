-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_beta_model_formula
-- name    : GivenDegreeSeq.MLE.beta_model_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:20.980012+00:00
-- url     : https://prove2.me/theorems/7c9421da-a4b4-4c44-acfa-e1d17edb1b0e
-- title:
--   p. 6 — $\mathbb P_\beta$ is a probability measure and $\mathbb P_\beta(G)=e^{\sum_i\beta_i d_i}/\prod_{i<j}(1+e^{\beta_i+\beta_j})$
-- statement:
--   Let $\beta\in\mathbb R^n$ and let $\mathbb P_\beta$ be the $\beta$-model, in which each edge $\{i,j\}$, $i\ne j$, is present independently with probability $p_{ij}=e^{\beta_i+\beta_j}/(1+e^{\beta_i+\beta_j})$. Then $\mathbb P_\beta$ is a probability measure on the simple graphs on $n$ vertices, and for every graph $G$ with degree sequence $d_1,\dots,d_n$,
--   $$\mathbb P_\beta(\{G\})=\frac{e^{\sum_i\beta_i d_i}}{\prod_{i<j}\big(1+e^{\beta_i+\beta_j}\big)}.$$
--
--   The formula shows that the $\beta$-model is an exponential family with the degree sequence as sufficient statistic; it links the independent-edge description of $\mathbb P_\beta$ to its likelihood, from which the ML equations (3) arise.
--
--   **Formalization Note** The probability-measure conjunct is implicit in the paper ("the law"); it is stated here because the definition of $\mathbb P_\beta$ as a finite sum of point masses does not carry it.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 6 (also restated on p. 16)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_BetaModel

open MeasureTheory

namespace GivenDegreeSeq.MLE

/-- p. 6. `P_β` is a probability measure on the simple graphs on `n` vertices, and the
probability of observing a given graph `G` with degree sequence `d_1, …, d_n` is
`e^{Σ_i β_i d_i} / ∏_{i<j} (1 + e^{β_i+β_j})`. -/
theorem beta_model_formula (n : ℕ) (β : Fin n → ℝ) :
    IsProbabilityMeasure (betaModel β) ∧
    ∀ G : SimpleGraph (Fin n),
      betaModel β {G} =
        ENNReal.ofReal (Real.exp (∑ i, β i * deg G i) /
          ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j => i < j),
            (1 + Real.exp (β i + β j))) := by sorry

end GivenDegreeSeq.MLE
