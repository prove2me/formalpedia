-- Prove2me | Theorems.Thm_MultiPurchaseMNL_running_time
-- name    : MultiPurchaseMNL.running_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:00.20336+00:00
-- url     : https://prove2.me/theorems/54cdf84e-fe5e-4cfc-a1b1-4b15706d1b77
-- title:
--   §4.3, p.19 — running time $O(n^{O(m_{\max}^2/\epsilon)})$
-- statement:
--   There are universal constants $C,K$ such that for every instance of the Multi-Purchase MNL assortment problem with $M$ supported on $\{0,\dots,m_{\max}\}$ and every $\varepsilon>0$, the program `ptas` performs at most
--   $$
--   K\cdot\max(n,2)^{C\,m_{\max}^2/\varepsilon}
--   $$
--   unit-cost operations. This is the paper's count: $O(n^{O(m^2_{\max}/\epsilon)})$ guesses of the heavy set, $O(n\cdot\frac{m_{\max}}{\epsilon}\log n)$ guesses of $W$, $O(n^{O(1)}2^{O(m_{\max}/\epsilon)})$ time for the estimators and $O(n^2m_{\max}/\epsilon)$ for the knapsack, plus the exact evaluation of every candidate.
--
--   Differences from the source:
--
--   - reading: O(n^{O(m²max/ϵ)}) time for the algorithm → ∃ universal C, K : ℕ with ops ≤ K·max(n,2)^{C·m²_max/ε} for the instrumented program ptas in the unit-cost real RAM; reason: the meaning of the O-notation with constants independent of n, m_max, ε and the data; max(n,2) reads n → ∞ and keeps the base ≥ 2
--   - reading: the itemized count of Step 1 and Step 2 → the count also includes the exact evaluation of every candidate's revenue by the recursion of Lemma 1; reason: the program selects among candidates by exact revenue (reading 5); this costs n^{O(m_max)} per candidate and stays within the bound
--   - generalization: m_max = O(1), M over [n]₀ → any m_max ≥ 1, not bounded by n; reason: the bound is uniform in m_max; the paper's case is a special one
--   - generalization: rᵢ > 0 (p.12) → rᵢ ≥ 0 (Standing.r_nonneg); reason: every instance with positive revenues satisfies it
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §4.3, p.19, "Running time"

import Mathlib
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_Algorithm

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §4.3, p.19, "Running time": "All
together, we arrive at an overall running time of `O(n^{O(m²max/ϵ)})`, as stated in Theorem 1."

There are universal constants `C`, `K` such that for every instance with `M` supported on
`{0, …, m_max}` and every `ε > 0`, the program `ptas` performs at most
`K · max(n, 2)^{C·m²_max/ε}` unit-cost operations.

**Formalization Note.** `C` and `K` are quantified before `n`, `m_max`, the data and `ε`. The base
`max(n, 2)` reads `n` as `n → ∞`. The count includes exact evaluation of the candidates' revenues by
the recursion of Lemma 1 (`n^{O(m_max)}` per candidate), which the paper's itemized count leaves out.
The power is `Real.rpow`. -/
theorem running_time :
    ∃ C K : ℕ, ∀ {n mmax : ℕ} (I : Instance n mmax), I.Standing → ∀ ε : ℝ, 0 < ε →
      (ops I ε : ℝ) ≤ K * (max (n : ℝ) 2) ^ ((C : ℝ) * mmax ^ 2 / ε) := by sorry

end MultiPurchaseMNL
