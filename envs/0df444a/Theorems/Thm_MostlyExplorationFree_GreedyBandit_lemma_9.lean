-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_9
-- name    : MostlyExplorationFree.GreedyBandit.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:38.760994+00:00
-- url     : https://prove2.me/theorems/09c104e7-0341-4ded-9699-57f657246465
-- title:
--   Lemma 9, p. 39 (Tropp 2011, Thm 3.1) — matrix Chernoff bound for adapted sequences of PSD matrices
-- statement:
--   Let $\mathcal H_0 \subseteq \mathcal H_1 \subseteq \cdots$ be a filtration on a probability space, and let $X_1, \dots, X_n$ be random $d \times d$ real matrices ($d \ge 1$), each $X_k$ being $\mathcal H_k$-measurable, positive semidefinite almost surely and with $\lambda_{\max}(X_k) \le R$ almost surely for a constant $R > 0$. Put
--   $$
--   Y = \sum_{k=1}^n X_k, \qquad W = \sum_{k=1}^n \mathbb E[X_k \mid \mathcal H_{k-1}].
--   $$
--   Then for all $\mu \ge 0$ and $\gamma \in [0, 1)$,
--   $$
--   \mathbb P\big[\lambda_{\min}(Y) \le (1-\gamma)\mu \ \text{ and } \ \lambda_{\min}(W) \ge \mu\big] \le d \left(\frac{e^{-\gamma}}{(1-\gamma)^{1-\gamma}}\right)^{\mu/R}.
--   $$
--
--   This is the adapted (martingale) version of the lower-tail matrix Chernoff inequality. It is the tool that turns the linear growth of the *conditional* covariance of an adaptively sampled arm into linear growth of its *sample* covariance. The independent special case is the classical matrix Chernoff inequality.
--
--   **Formalization Note** The conditional expectation is taken entrywise. Tropp states the result for Hermitian matrices; the real symmetric case is a special case. The paper leaves implicit that $R > 0$ (it divides by $R$) and $d \ge 1$; both are assumed.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 39, Lemma 9 (Theorem 3.1 of Tropp (2011), User-friendly tail bounds for matrix martingales)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_9 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 1 ≤ d) (ℱ : Filtration ℕ mΩ) (n : ℕ)
    (Xk : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (R : ℝ) (hR : 0 < R)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, ∀ a b, StronglyMeasurable[ℱ k] (fun ω => Xk k ω a b))
    (hpsd : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, (Xk k ω).PosSemidef)
    (hmax : ∀ k ∈ Finset.Icc 1 n, ∀ᵐ ω ∂P, lambdaMax (Xk k ω) ≤ R)
    (mu γ : ℝ) (hmu : 0 ≤ mu) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (P {ω | lambdaMin (∑ k ∈ Finset.Icc 1 n, Xk k ω) ≤ (1 - γ) * mu ∧
        mu ≤ lambdaMin (∑ k ∈ Finset.Icc 1 n, condExpMatrix (ℱ (k - 1)) P (Xk k) ω)}).toReal
      ≤ d * (Real.exp (-γ) / (1 - γ) ^ (1 - γ)) ^ (mu / R) := by sorry

end MostlyExplorationFree.GreedyBandit
