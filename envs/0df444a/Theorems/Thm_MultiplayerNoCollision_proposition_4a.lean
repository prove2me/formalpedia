-- Prove2me | Theorems.Thm_MultiplayerNoCollision_proposition_4a
-- name    : MultiplayerNoCollision.proposition_4a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:24.896575+00:00
-- url     : https://prove2.me/theorems/26fc8afe-a242-4392-8a22-b6e9f4d63265
-- title:
--   Proposition 4(a) — Hoeffding: $P\{|\hat\mu-\mu|>t\}<2e^{-2nt^2/b^2}$
-- statement:
--   Let $X_1,\dots,X_n$ ($n\ge1$) be independent random variables with $0\le X_k\le b$ for each $k$, for some fixed $b>0$. Let $\hat\mu=\sum_k X_k/n$ and $\mu=\mathbb E\hat\mu$. Then for every $t\ge0$,
--   $$P\{|\hat\mu-\mu|>t\}<2\exp\!\left(-\frac{2nt^2}{b^2}\right).$$
--
--   This is the concentration inequality used in Lemma 5 for the empirical average of the rewards from one arm, with $b=4$ after scaling.
--
--   Differences from the source:
--   - encoding: n, b unspecified ("some fixed b") → n ≥ 1 and b > 0; reason: the average divides by n and the bound by b²; only undefined cases are excluded
--   - encoding: independent random variables with 0 ≤ X_k ≤ b → measurable X_k, mutually independent (iIndepFun), 0 ≤ X_k ≤ b at every outcome; reason: standard convention; a null-set modification changes no probability
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, Proposition 4(a), p.9

import Mathlib

namespace MultiplayerNoCollision

open MeasureTheory ProbabilityTheory

/-- **Proposition 4(a) (Hoeffding's inequality, strict form).**
Lugosi, Mehrabian, *Multiplayer bandits without observing collision information*,
arXiv:1808.08416v2, Proposition 4(a), p.9 (citing [20, Theorem 2.3]): "Let the random variables
`X_1, …, X_n` be independent, with `0 ≤ X_k ≤ b` for each `k` and some fixed `b`. Let
`µ̂ = ∑ X_k / n` and `µ = E µ̂`. Then we have, (a) for any `t ≥ 0`,
`P{|µ̂ − µ| > t} < 2 exp(−2nt²/b²)`."

**Formalization Note.** `n ≥ 1` (the average divides by `n`) and `b > 0` (the bound divides by
`b²`) are stated explicitly. The random variables are measurable functions with
`0 ≤ X_k ≤ b` at every outcome; independence is mutual independence `iIndepFun`. The probability is
`P.real`, the real-valued measure. The inequality is strict, as printed. -/
theorem proposition_4a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (X : Fin n → Ω → ℝ) (hX_meas : ∀ k, Measurable (X k))
    (hX_indep : iIndepFun X P) (b : ℝ) (hb : 0 < b) (hX : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ b)
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t < |(∑ k, X k ω) / n - ∫ ω', (∑ k, X k ω') / n ∂P|} <
      2 * Real.exp (-2 * n * t ^ 2 / b ^ 2) := by sorry

end MultiplayerNoCollision
