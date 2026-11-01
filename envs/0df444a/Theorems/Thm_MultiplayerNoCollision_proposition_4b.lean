-- Prove2me | Theorems.Thm_MultiplayerNoCollision_proposition_4b
-- name    : MultiplayerNoCollision.proposition_4b
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:26.608003+00:00
-- url     : https://prove2.me/theorems/3bb79f2f-9d68-44ca-917f-1dc45b11bc43
-- title:
--   Proposition 4(b) — multiplicative Chernoff lower tail: $P\{\hat\mu<(1-\varepsilon)\mu\}<e^{-\varepsilon^2n\mu/2}$
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent random variables with $0\le X_k\le 1$. Let $\hat\mu=\sum_k X_k/n$ and $\mu=\mathbb E\hat\mu$. Then for every $\varepsilon>0$,
--   $$P\{\hat\mu<(1-\varepsilon)\mu\}<\exp\!\left(-\frac{\varepsilon^2n\mu}{2}\right).$$
--
--   In Lemma 5 it bounds the probability that an arm has been pulled fewer than $t/(2K)$ times in $t$ uniform rounds.
--
--   Differences from the source:
--   - encoding: n unspecified → n ≥ 1; reason: the average divides by n; only the undefined case is excluded
--   - encoding: independent random variables with 0 ≤ X_k ≤ b, b = 1 → measurable X_k, mutually independent (iIndepFun), 0 ≤ X_k ≤ 1 at every outcome; reason: standard convention; a null-set modification changes no probability
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Proposition 4(b), p.9

import Mathlib

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Proposition 4(b) (multiplicative Chernoff bound, lower tail, strict form).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Proposition 4(b), p.9 (citing [20, Theorem 2.3]): "Let the random variables
`X_1, …, X_n` be independent, with `0 ≤ X_k ≤ b` for each `k` and some fixed `b`. Let
`µ̂ = ∑ X_k / n` and `µ = E µ̂`. Then we have, … (b) and if `b = 1`, then for any `ε > 0`,
`P{µ̂ < (1 − ε)µ} < exp(−ε²nµ/2)`."

**Formalization Note.** This item states part (b) under the shared hypotheses of Proposition 4 with
`b = 1`. `n ≥ 1` (the average divides by `n`) is stated explicitly. The random variables are
measurable with `0 ≤ X_k ≤ 1` at every outcome; independence is `iIndepFun`. The probability is
`P.real`. Both the event `µ̂ < (1 − ε)µ` and the bound are strict, as printed. -/
theorem proposition_4b {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (hX_meas : ∀ k, Measurable (X k))
    (hX_indep : iIndepFun X P) (hX : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω | (∑ k, X k ω) / n < (1 - ε) * ∫ ω', (∑ k, X k ω') / n ∂P} <
      Real.exp (-(ε ^ 2 * n * ∫ ω', (∑ k, X k ω') / n ∂P) / 2) := by sorry

end MultiplayerNoCollision
