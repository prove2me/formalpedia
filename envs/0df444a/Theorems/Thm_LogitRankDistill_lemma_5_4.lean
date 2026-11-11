-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_4
-- name    : LogitRankDistill.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:32.826564+00:00
-- url     : https://prove2.me/theorems/b845eb6a-98d8-4bfb-b847-7a051a9bde1c
-- title:
--   Lemma 5.4 — all DistSpanner calls return distributional spanners with probability at least 1 − δ/2
-- statement:
--   Let DistSpanner draw $m(N)\ge C_m(N/\eta)^2\log(N/(\delta'\eta))$ samples for dimension $N$, with $\delta'=\delta/(10KT)$ (Algorithm 3 called on Line 7 with $\eta,\delta/(10KT)$; $C_m$ the constant of Lemma 5.2), and $\beta=2$. Then
--   $$\Pr\big[E_{\mathrm{spanner}}\big]\ge1-\delta/2,$$
--   where $E_{\mathrm{spanner}}$ is the event that at every epoch $k\in[K]$ and step $t$ the call on Line 7 returns an $(\eta,\beta)$-distributional spanner for $P_t$.
--
--   **Formalization Note.** One universal $C_m$; the statement holds for every model $M$, every oracle, all parameters $K,n,\gamma_{\mathrm{thres}}$ and every admissible choice of rules; the probability is over the stream of draws (outer measure of the complement $\le\delta/2$).
--
--   Differences from the source:
--   - generalization: the parameters of §5.2 with m = Θ((N/η)² log(N/(δ′η))) → any parameters with β = 2, η > 0, δ ∈ (0, 1) and m(N) ≥ C_m (N/η)² log(N/(δ′η)); every model, oracle and admissible rule set; reason: the proof uses only the lower bound on m (Lemma 5.2) and a union bound; §5.2 is a special case
--   - reading: E_spanner: "the call to DistSpanner on Line 7 … for all epochs k ∈ [K] and steps t ∈ [T]" → steps t ∈ {2, …, T} of every executed epoch; reason: Line 7 calls DistSpanner only for t ≥ 2; epochs after the return are not executed
--   - encoding: occurs with probability at least 1 − δ/2 → outer measure of its complement ≤ δ/2; reason: equivalent formulation
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 24, Lemma 5.4

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.4** (p. 24): `E_spanner` occurs with probability at least `1 − δ/2`, when DistSpanner
draws `m ≥ C_m (N/η)² log(N/(δ'η))` samples (`δ' = δ/(10KT)`, Algorithm 3 with Lemma 5.2's
constant) and `β = 2` (§5.2). Stated for every model `M`, every oracle and every admissible choice
of rules; the probability is over the stream of draws. -/
theorem lemma_5_4 :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
      [MeasurableSingletonClass Tok] (T : ℕ) (M : PMF (Fin T → Tok)) (O : List Tok → Tok → ℝ)
      (p : Params) (R : Rules Tok), 1 ≤ T → p.β = 2 → 0 < p.η → 0 < p.δ → p.δ < 1 →
      MLower Cm T p → R.Admissible →
      streamLaw M {ω | ¬ (⟨T, O, ω, p, R⟩ : Ctx Tok).SpannerEvent M} ≤
        ENNReal.ofReal (p.δ / 2) := by sorry

end LogitRankDistill
