-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_8
-- name    : MostlyExplorationFree.GreedyBandit.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:30:56.35899+00:00
-- url     : https://prove2.me/theorems/506d8137-3b38-4eba-b5df-d62511aba03a
-- title:
--   Lemma 8, p. 39 — Bernstein (Azuma–Hoeffding) bound ℙ[|Σ D_k| ≥ t] ≤ 2exp(−t²/(2Σσ_k²)) for sub-Gaussian martingale differences
-- statement:
--   Let $(\mathcal H_k)_{k \ge 0}$ be a filtration and $D_1, \dots, D_n$ real random variables with $D_k$ $\mathcal H_k$-measurable and conditionally $\sigma_k$-sub-Gaussian given $\mathcal H_{k-1}$:
--   $$
--   \mathbb E\big[e^{\tau D_k} \mid \mathcal H_{k-1}\big] \le e^{\sigma_k^2 \tau^2/2} \quad \text{almost surely, for every } \tau \in \mathbb R .
--   $$
--   (In particular $(D_k)$ is a martingale difference sequence.) Then for every $t > 0$,
--   $$
--   \mathbb P\Big[\Big|\sum_{k=1}^n D_k\Big| \ge t\Big] \le 2\exp\Big(-\frac{t^2}{2\sum_{k=1}^n \sigma_k^2}\Big).
--   $$
--
--   This concentration inequality for adaptively generated noise sums is what controls the least-squares error of an arm whose samples were selected by the algorithm itself.
--
--   **Formalization Note** The paper says "$D_k$ is $\sigma_k$-subgaussian" for a martingale difference sequence; the cited proof (Wainwright 2019, Theorem 2.3) uses the conditional form, which is stated here (with integrability of $e^{\tau D_k}$). If $\sum_k \sigma_k^2 = 0$, Lean's division by zero makes the right-hand side $2$, which still bounds the probability.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 39, Lemma 8 (Bernstein Concentration; proof: Wainwright (2019), Theorem 2.3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_8 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (D : ℕ → Ω → ℝ) (σk : ℕ → ℝ) (n : ℕ)
    (hadapted : ∀ k ∈ Finset.Icc 1 n, StronglyMeasurable[ℱ k] (D k))
    (hint : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ, Integrable (fun ω => Real.exp (τ * D k ω)) P)
    (hsubG : ∀ k ∈ Finset.Icc 1 n, ∀ τ : ℝ,
      condExp (ℱ (k - 1)) P (fun ω => Real.exp (τ * D k ω))
        ≤ᵐ[P] fun _ => Real.exp (σk k ^ 2 * τ ^ 2 / 2))
    (t : ℝ) (ht : 0 < t) :
    (P {ω | t ≤ |∑ k ∈ Finset.Icc 1 n, D k ω|}).toReal
      ≤ 2 * Real.exp (-(t ^ 2 / (2 * ∑ k ∈ Finset.Icc 1 n, σk k ^ 2))) := by sorry

end MostlyExplorationFree.GreedyBandit
