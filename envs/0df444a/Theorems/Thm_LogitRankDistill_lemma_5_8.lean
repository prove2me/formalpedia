-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_8
-- name    : LogitRankDistill.lemma_5_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:35.607852+00:00
-- url     : https://prove2.me/theorems/86e6b069-37fe-428a-94b4-881466a48713
-- title:
--   Lemma 5.8 — at a passing epoch the next-token logits of the program are within t·γ_thres + ε_apx of the true logits in expectation
-- statement:
--   Under the event $E_{5.7}$ of Lemma 5.7: for every epoch at which the if statement on Line 14 is False for all $t$, with $L_{1:T,1:\bar d}$ its spanners, for each $t$
--   $$\mathbb E_{Q_t(L_{1:t,1:\bar d})}\Big[\mathbf 1\{y_{1:t}\in G_t\}\cdot\min\Big\{1,\max_{y'\in\Sigma}\big|L(y_{1:t}\circ y')-\hat L_{t+1}(y')\big|\Big\}\Big]\le t\,\gamma_{\mathrm{thres}}+\varepsilon_{\mathrm{apx}},$$
--   where $L=L_M$ and $\hat L_{t+1}(y')=\sum_ic_{t,i}L_{t,i}(y_t\circ y')$. Combined with Lemmas 5.3 and 5.5 it gives the per-step bound (32).
--
--   **Formalization Note.** Stated for every run with $O$ an $\varepsilon_{\mathrm{apx}}$-approximate oracle and admissible rules, and every executed passing epoch at which (21) holds at every step $t\in[T-1]$ — the property $E_{5.7}$ provides.
--
--   Differences from the source:
--   - generalization: under the event E_5.7 of Lemma 5.7 → at every passing epoch at which (21) holds for every step; reason: on E_5.7, (21) holds at every passing epoch (Lemma 5.7), so this implies the printed statement
--   - reading: for each t ∈ [T] → t ∈ [T − 1]; reason: at t = T the sequence y_{1:T} ∘ y′ exceeds the horizon and Q_T would draw y_{T+1}
--   - generalization: the setting of §5.2 (its parameters, full-support M) → any parameters and every admissible choice rule set; M need not have full support; reason: the bound follows from (21) and the oracle accuracy; the §5.2 setting is a special case
--   - reading: Algorithm 1, Line 14: s, r ∈ [t + 1] with r ≥ s → the test ranges over 2 ≤ s ≤ t, s ≤ r ≤ t + 1 (LogitRankDistill.Algorithms); reason: at s = 1 the tested difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no coefficients c_{t+1} exist
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 28, Lemma 5.8

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.8** (p. 28): under `E_{5.7}`, for any epoch whose Line 14 test is False at every step,
for each step `t`:
`E_{Q_t}[1{y_{1:t} ∈ G_t} · min{1, max_{y'} |L(y_{1:t} ∘ y') − L̂_{t+1}(y')|}] ≤ t γ_thres + ε_apx`.
Stated for every run and every passing epoch at which the bound (21) of Lemma 5.7 holds at every
step (which is what `E_{5.7}` provides), with `O` an `ε_apx`-approximate oracle; steps
`t ∈ [T − 1]`. -/
theorem lemma_5_8 {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (C : Ctx Tok)
    (M : PMF (Fin C.T → Tok)) (εapx : ℝ) (hO : IsApproxOracle M εapx C.O)
    (hR : C.R.Admissible) (e : Epoch Tok) (he : e ∈ C.run.epochs)
    (hpass : e.outcome = Outcome.passed)
    (h21 : ∀ t, 1 ≤ t → t + 1 ≤ C.T → expect M (C.integrand21 e t) ≤ C.p.γthres) :
    ∀ t, 1 ≤ t → t + 1 ≤ C.T →
      expect M (C.integrand58 M e t) ≤ t * C.p.γthres + εapx := by sorry

end LogitRankDistill
