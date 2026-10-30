-- Prove2me | Theorems.Thm_MohriFoML_OnlineToBatch_hoeffding_inequality
-- name    : MohriFoML.OnlineToBatch.hoeffding_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:09:08.884046+00:00
-- url     : https://prove2.me/theorems/14b628e9-c865-4483-9bb6-98611204b6b1
-- title:
--   Theorem D.2 — Hoeffding's inequality, both tails
-- statement:
--   Let $X_1, \dots, X_m$ be independent real random variables on a probability space, with $X_i$ taking values in $[a_i, b_i]$ for every $i \in [m]$, and let $S_m = \sum_{i=1}^m X_i$. Then for every $\epsilon > 0$,
--
--   $$
--   P\big[S_m - \mathbb{E}[S_m] \ge \epsilon\big] \le e^{-2\epsilon^2 / \sum_{i=1}^m (b_i - a_i)^2}, \qquad P\big[S_m - \mathbb{E}[S_m] \le -\epsilon\big] \le e^{-2\epsilon^2 / \sum_{i=1}^m (b_i - a_i)^2} .
--   $$
--
--   Hoeffding's inequality is the basic concentration bound for sums of bounded independent variables. In Section 8.4 it controls the empirical loss of a single fixed hypothesis on the i.i.d. sample in the proof of (8.28).
--
--   **Formalization Note** Independence is mutual independence; each $X_i$ is measurable and lies in $[a_i, b_i]$ at every point; indices are 0-based in Lean.
--
--   Differences from the source:
--   - encoding: e^{−2ε²/Σ(b_i−a_i)²} with Σ(b_i−a_i)² = 0 (undefined) → exp(0) = 1; reason: Lean's x / 0 = 0; then every X_i is constant, both events are empty, and the bound holds trivially
--   - encoding: X_1, …, X_m, i ∈ [m] → X i for i : Fin m (0-based); reason: Lean convention; same instances
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 438 (PDF p. 455), Appendix D §D.1, Theorem D.2 (Hoeffding's inequality), (D.4)–(D.5)

import Mathlib

namespace MohriFoML.OnlineToBatch

open MeasureTheory ProbabilityTheory

/-- **Theorem D.2: Hoeffding's inequality (both tails).**
Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018,
Appendix D, §D.1, p. 438 (PDF p. 455), Theorem D.2, inequalities (D.4)–(D.5).

Let `X_1, …, X_m` be independent random variables with `X_i` taking values in `[a_i, b_i]` for all
`i ∈ [m]`, and `S_m = ∑_{i=1}^m X_i`. Then for any `ε > 0`,
`P[S_m − E[S_m] ≥ ε] ≤ e^{−2ε²/∑_{i=1}^m (b_i−a_i)²}` and
`P[S_m − E[S_m] ≤ −ε] ≤ e^{−2ε²/∑_{i=1}^m (b_i−a_i)²}`.

**Formalization Note.** Indices are 0-based (`Fin m`). The `X_i` are measurable real functions on
a probability space, mutually independent (`iIndepFun`), with `a_i ≤ X_i ≤ b_i` at every point;
`E[S_m]` is the Bochner integral of `S_m` (which is integrable). When `∑ (b_i − a_i)² = 0`, Lean's
`x / 0 = 0` makes the bound `exp 0 = 1`, which holds trivially. -/
theorem hoeffding_inequality {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ}
    (X : Fin m → Ω → ℝ) (a b : Fin m → ℝ)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hX : ∀ i ω, X i ω ∈ Set.Icc (a i) (b i)) :
    ∀ ε : ℝ, 0 < ε →
      μ.real {ω | ε ≤ (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i, (b i - a i) ^ 2) ∧
        μ.real {ω | (∑ i, X i ω) - ∫ ω', (∑ i, X i ω') ∂μ ≤ -ε}
          ≤ Real.exp (-2 * ε ^ 2 / ∑ i, (b i - a i) ^ 2) := by sorry

end MohriFoML.OnlineToBatch
