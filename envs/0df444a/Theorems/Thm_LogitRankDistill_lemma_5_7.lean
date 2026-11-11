-- Prove2me | Theorems.Thm_LogitRankDistill_lemma_5_7
-- name    : LogitRankDistill.lemma_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:59:38.728211+00:00
-- url     : https://prove2.me/theorems/3adde53c-0132-4997-b11e-fefba2f926f9
-- title:
--   Lemma 5.7 — with n ≥ C_n log(TK/δ)·Kβα/γ_thres, on E_5.7 every passing epoch satisfies (21) at every step
-- statement:
--   Suppose $n\ge C_n\log(TK/\delta)\cdot(K\beta\alpha/\gamma_{\mathrm{thres}})$ for a sufficiently large constant $C_n$. There is an event $E_{5.7}$ with $\Pr[E_{5.7}]\ge1-\delta/4$ such that on $E_{5.7}$, for every epoch $k$ at which the if statement on Line 14 is False for all $t$, the spanners $L_{1:T,1:\bar d}$ of that epoch satisfy, for every $t$,
--   $$\mathbb E_{Q_t(L_{1:t,1:\bar d})}\Big[\mathbf 1\{y_{1:t}\in G_t\}\cdot\min\Big\{1,\max_{s,r,\,y'_r}\Big|\hat L_s(y_{s:r-1},y'_r)-\sum_{i=1}^{\bar d}c_{s,i}L_{s,i}(y_{s:r-1},y'_r)\Big|\Big\}\Big]\le\gamma_{\mathrm{thres}}.\qquad(21)$$
--   It converts the empirical Line 14 test into the in-expectation bound used by Lemma 5.8.
--
--   **Formalization Note.** $Q_t$ draws $y\sim M$ and takes the solution rule's $c$ (Definition 5.5); $\hat L_s$ is the Line 13 extension. The maximum is over $2\le s\le t$, $s\le r\le t+1$, $y'_r\in\Sigma$; steps $t\in[T-1]$.
--
--   Differences from the source:
--   - generalization: the setting of §5.2 (parameters, ε_apx-approximate oracle) → any model, any oracle, any parameters with γ_thres > 0 and the printed bound on n, δ ∈ (0,1), α > 0; reason: the statement involves only n, K, β, α, γ_thres, δ; the §5.2 setting is a special case
--   - reading: max over s, r ∈ [t + 1], r ≥ s → 2 ≤ s ≤ t, s ≤ r ≤ t + 1; reason: at s = 1 the difference is 0 (c_1 = e_1, L_{1,i} = L_oracle(·)); at s = t + 1 no c_{t+1} exists
--   - reading: for all t ∈ [T] → t ∈ [T − 1]; reason: Line 14 is evaluated only for t ≤ T − 1, and Q_t draws y_{1:t+1}
--   - encoding: an event E_5.7 with probability ≥ 1 − δ/4 → a measurable set of streams whose complement has measure ≤ δ/4; reason: equivalent formulation
--   - generalization: Algorithm 1 with its unspecified choices (spanner, program solution, Line 15 witness) → every admissible choice rule set; reason: every implementation of Algorithm 1 makes some admissible choices, so this specializes to it
--   - reading: F̃_T = F̂_T ∪ (Σ ∘ F̂_{T+1}) with F̂_{T+1} never initialized; DistSpanner output "padded with duplicates" to d̄ vectors → F̂_{T+1} = ∅; the padding repeats the first spanner member; reason: Line 1 initializes F̂_t only for t ∈ [T]; any duplicate of a member leaves the spanned set unchanged
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 27, Lemma 5.7

import Mathlib
import Definitions.Def_LogitRankDistill_Models
import Definitions.Def_LogitRankDistill_Spanners
import Definitions.Def_LogitRankDistill_Algorithms

open MeasureTheory

namespace LogitRankDistill

/-- **Lemma 5.7** (p. 27): if `n ≥ C_n log(TK/δ) (Kβα/γ_thres)` for a sufficiently large constant
`C_n`, there is an event `E_{5.7}` of probability at least `1 − δ/4` on which, for every epoch
whose Line 14 test is False at every step, the bound (21) holds at every step `t`:
`E_{Q_t}[1{y_{1:t} ∈ G_t} · min{1, max_{s,r,y'_r} |L̂_s(y_{s:r−1}, y'_r) − ∑_i c_{s,i} L_{s,i}(y_{s:r−1}, y'_r)|}] ≤ γ_thres`.
Steps are `t ∈ [T − 1]` (those at which Line 14 is evaluated, and `Q_t` draws `y_{1:t+1}`). -/
theorem lemma_5_7 :
    ∃ Cn : ℝ, 0 < Cn ∧
    ∀ (Tok : Type) [Fintype Tok] [DecidableEq Tok] [MeasurableSpace Tok]
      [MeasurableSingletonClass Tok] (T : ℕ) (α δ : ℝ) (M : PMF (Fin T → Tok))
      (O : List Tok → Tok → ℝ) (p : Params) (R : Rules Tok),
      1 ≤ T → 0 < α → 0 < δ → δ < 1 → 0 < p.γthres →
      Cn * Real.log (T * p.K / δ) * (p.K * p.β * α / p.γthres) ≤ p.n → R.Admissible →
      ∃ E : Set (ℕ → Fin T → Tok), MeasurableSet E ∧
        streamLaw M Eᶜ ≤ ENNReal.ofReal (δ / 4) ∧
        ∀ ω ∈ E, ∀ e ∈ (⟨T, O, ω, p, R⟩ : Ctx Tok).run.epochs, e.outcome = Outcome.passed →
          ∀ t, 1 ≤ t → t + 1 ≤ T →
            expect M ((⟨T, O, ω, p, R⟩ : Ctx Tok).integrand21 e t) ≤ p.γthres := by sorry

end LogitRankDistill
