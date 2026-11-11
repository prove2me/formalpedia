-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_10
-- name    : LogitRankDistill.lemma_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:34.651366+00:00
-- url     : https://prove2.me/theorems/24ebd8dc-4874-4ab8-9564-fdd697535ea4
-- title:
--   Lemma 5.10 — Algorithm 1 makes Õ(K⁴T|Σ| log(1/δ)/η² + nT³K²|Σ|) queries to M and O_logit
-- statement:
--   Algorithm 1 can be implemented using
--   $$\tilde O\Big(K^4T|\Sigma|\log(1/\delta)/\eta^2+nT^3K^2|\Sigma|\Big)$$
--   queries to $M$ and $O_{\mathrm{logit}}$. Read with explicit constants: for DistSpanner's $m(N)\le C_m(N/\eta)^2\log(N/(\delta'\eta))+C_m$ there are $C,k$ (depending only on $C_m$) such that every run, with every oracle and every admissible choice of rules, makes at most
--   $$C\Big(\frac{K^4T|\Sigma|\log(1/\delta)}{\eta^2}+nT^3K^2|\Sigma|\Big)\log\Big(2+\frac{KTn|\Sigma|}{\eta\delta}\Big)^k$$
--   oracle calls plus draws from $M$.
--
--   **Formalization Note.** The count is the length of the recorded oracle trace (one call per $L_{\mathrm{oracle}}$ evaluation) plus the number of stream cells read. $K\ge1$, $\eta,\delta\in(0,1)$.
--
--   Differences from the source:
--   - reading: Õ(·) → C·(…)·log(2 + KTn|Σ|/(ηδ))^k with C, k depending only on DistSpanner's constant; reason: Õ hides polylogarithmic factors in the parameters
--   - generalization: DistSpanner with m = Θ((N/η)² log(N/(δ′η))) → any m(N) ≤ C_m (N/η)² log(N/(δ′η)) + C_m; reason: a query upper bound needs only the upper half of Θ
--   - generalization: "can be implemented" → every run of the formalized Algorithm 1, for every admissible choice of rules; reason: the bound for the given implementation implies existence of one
--   - reading: K, η, δ from §5.2 → K ≥ 1, η, δ ∈ (0, 1); reason: the standing ranges; at K = 0 the printed expression is 0 while Line 1 still draws once
--   - reading: Line 17 queries and stores L_oracle(h_{t,i} ∘ y) for y ∈ Σ → Line 17 also queries and stores L_oracle(h_{t,i} ∘ y ∘ y′), y, y′ ∈ Σ, for t ≤ T − 1, and these queries are counted; reason: Algorithm 2, Line 6 reads these values (finding I5)
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 30, Lemma 5.10

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

namespace LogitRankDistill

/-- **Lemma 5.10** (p. 30): Algorithm 1 can be implemented with
`Õ(K⁴ T |Σ| log(1/δ)/η² + n T³ K² |Σ|)` queries to `M` and `O_logit`. For DistSpanner's
`m = Θ((N/η)² log(N/(δ'η)))` (upper constant `C_m`), there are `C, k` (depending on `C_m` only)
such that every run makes at most
`C (K⁴ T |Σ| log(1/δ)/η² + n T³ K² |Σ|) · log(2 + KTn|Σ|/(ηδ))^k` oracle calls and draws from `M`
in total, for every oracle and every admissible choice of rules. -/
theorem lemma_5_10 :
    ∀ Cm : ℝ, 0 < Cm → ∃ (C : ℝ) (k : ℕ), 0 < C ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] (T : ℕ) (O : List Tok → Tok → ℝ)
      (ω : ℕ → Fin T → Tok) (p : Params) (R : Rules Tok),
      1 ≤ T → 1 ≤ p.K → 0 < p.η → p.η < 1 → 0 < p.δ → p.δ < 1 → MUpper Cm T p →
      R.Admissible →
      ((⟨T, O, ω, p, R⟩ : Ctx Tok).numQueries + (⟨T, O, ω, p, R⟩ : Ctx Tok).run.cur : ℝ) ≤
        C * ((p.K : ℝ) ^ 4 * T * Fintype.card Tok * Real.log (1 / p.δ) / p.η ^ 2 +
            p.n * (T : ℝ) ^ 3 * (p.K : ℝ) ^ 2 * Fintype.card Tok) *
          Real.log (2 + p.K * T * p.n * Fintype.card Tok / (p.η * p.δ)) ^ k := by sorry

end LogitRankDistill
