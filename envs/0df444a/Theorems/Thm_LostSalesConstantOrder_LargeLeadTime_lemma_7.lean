-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_lemma_7
-- name    : LostSalesConstantOrder.LargeLeadTime.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:20.44739+00:00
-- url     : https://prove2.me/theorems/88e4c58f-e409-4dc7-a685-f98e76ba2da2
-- title:
--   Lemma 7: the coupled lower bound on the cost of $\bar\pi$ through $i^{r^*}_k$
-- statement:
--   In the setting of Lemma 6 ($\pi$ never orders more than $Q$, $(\mathbf x^*,\mathcal I^*)$ solves (4)), let $r^*=L^{-1}\sum_{i=1}^Lx^*_i$, let $I^{r^*}_{1,\infty}$ be a copy of $I^{r^*}_\infty$ independent of the demands, and let $i^{r^*}_k$ be the largest index attaining $W^{r^*}_k$. For every period $\tau$, $\mathbb E[\sum_{t=\tau}^{\tau+L-1}C^{\pi}_t]$ is at least
--   $$
--   h\Big(\sum_{k=1}^L\mathbb E\Big[i^{r^*}_kr^*-\sum_{i=1}^{i^{r^*}_k}D_i\Big]+\sum_{k=1}^L\mathbb E\Big[\sum_{i=k+1-i^{r^*}_k}^kx^*_i\Big]-r^*\sum_{k=1}^L\mathbb E[i^{r^*}_k]\Big)+c\Big(\mathbb E[I^*_{L+1}]-\mathcal I^*+L\,\mathbb E[D]-\sum_{i=1}^Lx^*_i\Big).
--   $$
--
--   The coupling of $V_k$ with the index $i^{r^*}_k$ puts the lower bound in the same terms as the cost of the constant-order policy $\pi_{r^*}$ (Lemma 4).
--
--   **Formalization Note** As in Lemma 6, the statement is for every policy that never orders more than $Q$ (the paper's $\bar\pi$ is one) and every window start. The expectations are over the product of the law of $I^{r^*}_\infty$ and the demand law. No hypothesis $r^*<\mathbb E[D]$ is added (the paper states none); the integrands do not involve $I^{r^*}_{1,\infty}$ except through the index $i^{r^*}_k$. The real right-hand side is mapped into $[0,\infty]$ with `ENNReal.ofReal`.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 9, Lemma 7

import Definitions.Def_LostSalesConstantOrder_LargeLeadTime_RandomWalk

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Lemma 7, p. 9. Hypotheses as in Lemma 6; `r* = L⁻¹ Σ x*_i` and `i^{r*}_k` is built from an
independent pair `(I^{r*}_{1,∞}, (D_i))`. Then `E[Σ_{t=τ}^{τ+L−1} C_t^π]` is at least
`h(Σ_k E[i^{r*}_k r* − Σ_{i=1}^{i^{r*}_k} D_i] + Σ_k E[Σ_{i=k+1−i^{r*}_k}^k x*_i] − r* Σ_k E[i^{r*}_k])
+ c(E[I*_{L+1}] − 𝓘* + L E[D] − Σ x*_i)`, all sums over `k = 1, …, L`. -/
theorem lemma_7 (P : CappedBaseStock.DemandLaw) (prm : CappedBaseStock.Parameters)
    (h3 : FiniteThirdMoment P) (hnd : NonDeterministic P)
    (π : CappedBaseStock.AdmissiblePolicy) (hπ : OrdersBounded P π (Qlevel P prm))
    (x : Fin prm.L → ℝ≥0) (I : ℝ≥0) (hmin : IsWindowMinimizer P prm x I) (t₀ : ℕ) :
    ENNReal.ofReal
        (prm.h *
            ((∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ((ik (rStar x) k p.1 p.2 : ℝ) * (rStar x : ℝ) -
                  ∑ i ∈ Finset.Icc 1 (ik (rStar x) k p.1 p.2), (p.2 (i - 1) : ℝ)) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) +
              (∑ k ∈ Finset.Icc 1 prm.L,
                ∫ p, ∑ i ∈ Finset.Icc (k + 1 - ik (rStar x) k p.1 p.2) k, (slot x (i - 1) : ℝ) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) -
              (rStar x : ℝ) * ∑ k ∈ Finset.Icc 1 prm.L, ∫ p, (ik (rStar x) k p.1 p.2 : ℝ) ∂((lawSupWalk P (rStar x)).prod (CappedBaseStock.demandPathLaw P))) +
          prm.p * ((∫ d, (endInventory prm x I d : ℝ) ∂CappedBaseStock.demandPathLaw P) -
            I + prm.L * CappedBaseStock.mean P - ∑ i, (x i : ℝ))) ≤
      costWindow P prm π t₀ := by sorry

end LostSalesConstantOrder.LargeLeadTime
