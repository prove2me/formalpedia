-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_12
-- name    : LogitRankDistill.lemma_5_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:42.985487+00:00
-- url     : https://prove2.me/theorems/ef740e18-7d24-4e24-a26a-5181da81e829
-- title:
--   Lemma 5.12 — every query of Algorithm 1 is a splice y^{(j)}_{1:s−1} ∘ y′_s ∘ y^{(i)}_{s+1:t−1} of N i.i.d. samples
-- statement:
--   It is possible to couple the execution of Algorithm 1 with the draw of
--   $$N:=O\big(Kn+KT(K/\eta)^2\log(K/(\eta\delta))\big)$$
--   i.i.d. samples $y^{(1)}_{1:T},\dots,y^{(N)}_{1:T}\sim M$ so that each query to $O_{\mathrm{logit}}$ in Algorithm 1 is of the form $O_{\mathrm{logit}}(y^{(j)}_{1:s-1}\circ y'_s\circ y^{(i)}_{s+1:t-1})$ for some $i,j\in[N]$, $0\le s<t\le T$ and $y'_s\in\Sigma$.
--   This is what lets the average-case assumption of Definition 4.3 control every query in Theorem 5.14.
--
--   **Formalization Note.** The coupling is the run's own stream of i.i.d. draws: there is $C$ (depending on DistSpanner's constant) such that every run reads at most $C(Kn+KT(K/\eta)^2\log(K/(\eta\delta)))$ draws, and every query has the stated form with $i,j$ among the draws read.
--
--   Differences from the source:
--   - encoding: a coupling of the execution with N i.i.d. samples → Algorithm 1 reads its draws from an i.i.d. stream; the draws read are the samples; reason: the stream realises the coupling; the law of the run is unchanged
--   - reading: N = O(Kn + KT(K/η)² log(K/(ηδ))) → ∃ C (depending only on DistSpanner's constant) bounding the draws read by C(Kn + KT(K/η)² log(K/(ηδ))); reason: O(·) is a universal constant
--   - reading: s = 0: y^{(j)}_{1:−1} ∘ y′_0 ∘ y^{(i)}_{1:t−1} → at s = 0 the query is y^{(i)}_{1:t−1}; reason: there is no position 0; the prefix and y′_0 are empty
--   - generalization: DistSpanner with m = Θ(…) → any m(N) ≤ C_m (N/η)² log(N/(δ′η)) + C_m, every oracle and admissible rule set; reason: an upper bound needs only the upper half of Θ
--   - reading: Line 17 queries and stores L_oracle(h_{t,i} ∘ y) for y ∈ Σ → Line 17 also queries and stores L_oracle(h_{t,i} ∘ y ∘ y′), y, y′ ∈ Σ, for t ≤ T − 1, and these queries are counted; reason: Algorithm 2, Line 6 reads these values (finding I5)
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 32, Lemma 5.12

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

namespace LogitRankDistill

/-- **Lemma 5.12** (p. 32): the execution of Algorithm 1 can be coupled with
`N = O(Kn + KT(K/η)² log(K/(ηδ)))` i.i.d. draws `y^{(1)}, …, y^{(N)} ∼ M` so that every query to
`O_logit` is `y^{(j)}_{1:s−1} ∘ y'_s ∘ y^{(i)}_{s+1:t−1}` for some `i, j ∈ [N]`, `0 ≤ s < t ≤ T`,
`y'_s ∈ Σ`. The coupling is the stream itself: for DistSpanner's `m = Θ(…)` (upper constant `C_m`)
there is `C` with: every run reads at most `C(Kn + KT(K/η)² log(K/(ηδ)))` draws, and each query
has that form with `i, j` among the draws read (at `s = 0` the query is `y^{(i)}_{1:t−1}`). -/
theorem lemma_5_12 :
    ∀ Cm : ℝ, 0 < Cm → ∃ C : ℝ, 0 < C ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] (T : ℕ) (O : List Tok → Tok → ℝ)
      (ω : ℕ → Fin T → Tok) (p : Params) (R : Rules Tok),
      1 ≤ T → 1 ≤ p.K → 0 < p.η → p.η < 1 → 0 < p.δ → p.δ < 1 → MUpper Cm T p →
      R.Admissible →
      ((⟨T, O, ω, p, R⟩ : Ctx Tok).run.cur : ℝ) ≤
          C * (p.K * p.n + p.K * T * ((p.K : ℝ) / p.η) ^ 2 * Real.log (p.K / (p.η * p.δ))) ∧
      ∀ q ∈ (⟨T, O, ω, p, R⟩ : Ctx Tok).run.trace,
        ∃ i j s t : ℕ, ∃ y' : Tok, i < (⟨T, O, ω, p, R⟩ : Ctx Tok).run.cur ∧
          j < (⟨T, O, ω, p, R⟩ : Ctx Tok).run.cur ∧ s < t ∧ t ≤ T ∧
          q = (if s = 0 then seg (ω i) 1 (t - 1)
            else pre (ω j) (s - 1) ++ [y'] ++ seg (ω i) (s + 1) (t - 1)) := by sorry

end LogitRankDistill
