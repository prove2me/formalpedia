-- Prove2me | Theorems.Thm_MinSumFPT_lemma_11
-- name    : MinSumFPT.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:01.013817+00:00
-- url     : https://prove2.me/theorems/603bea67-5720-44d6-b365-c98044413fd4
-- title:
--   Lemma 11 (corrected: $c\le n^2$) — distance sampling hits the core at some level $i\le10\log_2(nk/\varepsilon)$
-- statement:
--   Under the assumptions and notation of Lemma 10 (target clustering $\sigma$ with $\Lambda\ge\mathrm{cost}(\sigma)$, $0<\varepsilon<1$, nonempty $M$, $C_j$ the least uncovered cluster), let $c\le n^2$. If
--
--   $$
--   \sum_{p\in A}d(p,m_p)\ \le\ c\cdot\Lambda,
--   $$
--
--   then there is an integer $i\ge0$ with $i\le10\log_2(nk/\varepsilon)$ such that
--
--   $$
--   P_i\big[p\in\mathrm{core}_2(C_j)\big]\ \ge\ \frac{\varepsilon\,\zeta}{2k},\qquad\zeta=\frac1{600}.
--   $$
--
--   So at one of the $10\log_2(nk/\varepsilon)$ levels explored by Algorithm 1, a sample from $P_i$ lies in the core of the largest uncovered cluster with probability at least $\varepsilon/(1200k)$. This drives the induction in the proof of Theorem 5.
--
--   **Formalization Note** The probability is in multiplied form with the weights $d(p,m_p)$.
--
--   Differences from the source:
--   - correction: c ≤ n⁹ → c ≤ n²; reason: false for c = n⁹: k = 3, ε = 1/2, a star metric around m₀ with C₁ = {m₀} ∪ s points at distance τ, C₂ = s points at distance D = Γ_I, C₃ = two points c₁, c₂ far out with d(c₁,c₂) tuned so cost(σ) = Λ = 120(s − 10)sτ, Σ_p d(p,m_p) = n⁹Λ (n = 2s + 3), M = {m₀}: C₁ is the least uncovered cluster, core₂(C₁) is the s near points, and for every i ≤ 10 log₂(6n), P_i[core₂(C₁)] ≤ τ/(τ + D) < ε/(3600) once s ≥ 10¹⁰; the proof's display (p.17) bounds Σ by n²·OPT, which works for c ≤ n²
--   - correction: OPT in (1) and in Σ_p d(p, m_p) ≤ c·OPT is the instance optimum, for an arbitrary target → Λ ≥ cost(𝒞); reason: as in Lemma 10 (same counterexample to the conditional bound the proof uses)
--   - generalization: ∃ a small absolute constant ζ > 0 → ζ = 1/600; reason: the proof fixes ζ ≤ 1/600 (p.16) and Eq. (11) uses ε/(600k); implies the existential
--   - reading: i ≤ 10 log(nk/ε) → (i : ℝ) ≤ 10 log₂(nk/ε); reason: Γ_i = 2^{−i}…; the proof's (ε/(nk))^{10} = 2^{−10 log₂(nk/ε)}
--   - encoding: the probability P_i[X : Y] (resp. P_i[X]) under P_{i,M} → the multiplied form c·w(Y ∩ A_i) ≤ w(X ∩ Y ∩ A_i) with w the weight d(p, m_p); reason: agrees with the ratio when the denominator is positive
--   - encoding: M a set of points (a non-empty node set, p.13) → M a nonempty Finset; reason: m_q needs M ≠ ∅
--   - reading: ε > 0 sufficiently small (ε < 1 definitely suffices) → 0 < ε < 1; reason: the page's own sufficient range
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 11, p.16 (constant c ≤ n⁹ corrected to n², the bound of the proof's display on p.17)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered
import Definitions.Def_MinSumFPT_wSum
open scoped Classical

namespace MinSumFPT

/-- Lemma 11 (corrected: `c ≤ n²`) (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Lemma 11, p.16), with ζ = 1/600: under the assumptions
of Lemma 10, if `c ≤ n²` and `∑_{p∈A} d(p, m_p) ≤ c ⋅ Λ`, then there is an `i ≤ 10 log₂(nk/ε)`
with `P_i[p ∈ core₂(C_j)] ≥ ε ⋅ ζ/(2k)`.

**Formalization Note.** OPT is `Λ` as in Lemma 10. The probability is in multiplied form
`(εζ/(2k)) ⋅ wSum(A_i) ≤ wSum(core₂(C_j) ∩ A_i)`. The logarithm is base 2 (Γ_i = 2^{−i}⋯ and the
proof's `(ε/(nk))^{10}`). The page's bound `c ≤ n⁹` is replaced by `c ≤ n²`, the bound its proof
uses (see the Differences). -/
theorem lemma_11 {n k : ℕ} (d : Fin n → Fin n → ℝ) (hd : MinSumClust.IsPseudometric d)
    (σ : Fin n → Fin k)
    (hsort : ∀ i j : Fin k, i ≤ j → (clusterOf σ j).card ≤ (clusterOf σ i).card)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (Λ : ℝ) (hΛ : labCost d σ ≤ Λ)
    (M : Finset (Fin n)) (hM : M.Nonempty) (j : Fin k)
    (hj : ¬ IsCovered d Λ k ε 5 M (clusterOf σ j))
    (hmin : ∀ j' : Fin k, j' < j → IsCovered d Λ k ε 5 M (clusterOf σ j'))
    (c : ℝ) (hc : c ≤ (n : ℝ) ^ 2) (hsum : ∑ p, distToSet d M hM p ≤ c * Λ) :
    ∃ i : ℕ, (i : ℝ) ≤ 10 * Real.logb 2 (n * k / ε) ∧
      ε * (1 / 600) / (2 * k) * wSum d M hM (levelSet d M hM i) ≤
        wSum d M hM (core d 2 (clusterOf σ j) ∩ levelSet d M hM i) := by sorry

end MinSumFPT
