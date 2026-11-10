-- Prove2me | Theorems.Thm_OptStochMatch_Tight_proposition_3_3
-- name    : OptStochMatch.Tight.proposition_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:53:38.484963+00:00
-- url     : https://prove2.me/theorems/0909f74f-062d-4422-b5cb-67897b5ecf0d
-- title:
--   Proposition 3.3 — the law of the maximum of a random supermodular function through chains
-- statement:
--   Let $d:2^{[m]}\to\mathbb R$ be a random supermodular function with $d(\emptyset)=0$ almost surely. For every $a\ge0$,
--   $$\mathbb P\Big(\max_{A\subseteq[m]}d(A)>a\Big)=\sum_{k=1}^m(-1)^{k-1}\sum_{\emptyset\neq A_1\subsetneq\cdots\subsetneq A_k\subseteq[m]}\mathbb P\big(d(A_r)>a\text{ for all }r\big).$$
--
--   Differences from the source:
--   - encoding: a random supermodular function → d : Ω → Finset (Fin m) → ℝ on a probability space, each d(·)(A) measurable, supermodular almost surely; reason: random supermodularity is imposed almost surely, allowing arbitrary null exceptional outcomes without changing any probability; this also includes the pointwise interpretation
--   - encoding: chains ∅ ≠ A_1 ⊊ ⋯ ⊊ A_k ⊆ [m] → strictly increasing maps Fin k → Finset (Fin m) with nonempty values; reason: same set of chains
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Proposition 3.3, p. 9 (PDF p. 10)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace OptStochMatch.Tight

/-- Proposition 3.3 (p. 9, PDF 10). Let `d : 2^[m] → ℝ` be a random supermodular function with
`d(∅) = 0` almost surely. For every `a ≥ 0`,
`P(max_{A ⊆ [m]} d(A) > a) = ∑_{k=1}^m (−1)^{k−1} ∑_{∅ ≠ A_1 ⊊ ⋯ ⊊ A_k ⊆ [m]} P(d(A_r) > a ∀ r)`.
Chains of length `k` are strictly increasing maps `Fin k → Finset (Fin m)` with nonempty
members. -/
theorem proposition_3_3 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → Finset (Fin m) → ℝ)
    (hd_meas : ∀ A : Finset (Fin m), Measurable fun ω => d ω A)
    (hsuper : ∀ᵐ ω ∂μ, ∀ A B : Finset (Fin m),
      d ω A + d ω B ≤ d ω (A ∪ B) + d ω (A ∩ B))
    (hempty : ∀ᵐ ω ∂μ, d ω ∅ = 0) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | a < Finset.univ.sup' Finset.univ_nonempty (d ω)} =
      ∑ k ∈ Finset.Icc 1 m, (-1 : ℝ) ^ (k - 1) *
        ∑ c ∈ (Finset.univ.filter fun c : Fin k → Finset (Fin m) =>
            StrictMono c ∧ ∀ r, (c r).Nonempty),
          μ.real {ω | ∀ r, a < d ω (c r)} := by sorry

end OptStochMatch.Tight
