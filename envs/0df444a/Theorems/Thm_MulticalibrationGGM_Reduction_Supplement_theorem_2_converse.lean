-- Prove2me | Theorems.Thm_MulticalibrationGGM_Reduction_Supplement_theorem_2_converse
-- name    : MulticalibrationGGM.Reduction.Supplement.theorem_2_converse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:41:02.369215+00:00
-- url     : https://prove2.me/theorems/d07312cb-fb41-469a-9cd1-f2146a9f0035
-- title:
--   Theorem 2 (Informal), second bullet (§2.1.1) — a multicalibrated forecaster solves EVIs by uniform mixing
-- statement:
--   Let $Y\subseteq\mathbb R^d$ be compact and convex, and let $H$ be a class of tests $h:X\times Y\to\mathbb R^d$, each bounded. Let $F$ be a forecaster and $B:\mathbb N\to\mathbb R$ a function with $B(T)/T\to0$. Assume $F$ is $H$-multicalibrated with error bound $B$ against adaptive Nature: for every $h\in H$, every Nature that may choose $y_t$ after seeing $D_t$, and every $T\ge1$,
--
--   $$\sum_{t=1}^T\mathbb E_{p_t\sim D_t}\big[h(x_t,p_t)^\top(y_t-p_t)\big]\le B(T).$$
--
--   Fix a context $x\in X$ and a test $h\in H$. Then:
--
--   1. There is a best-response Nature at $(x,h)$: one that plays $x_t=x$ and $y_t\in\arg\max_{\hat y\in Y}\hat y^\top\mathbb E_{p_t\sim D_t}[h(x,p_t)]$.
--   2. Take any best-response Nature at $(x,h)$ and any $T\ge1$, and suppose the coordinates of $h(x,\cdot)$ are integrable under the laws $D_1,\dots,D_T$ of its run with $F$. Let $\bar D_T=\frac1T\sum_{t=1}^TD_t$ be their uniform mixture. Then for every $y\in Y$ the payoff $p\mapsto h(x,p)^\top(y-p)$ is integrable under $\bar D_T$, and $$\mathbb E_{p\sim\bar D_T}\big[h(x,p)^\top(y-p)\big]\le\frac{B(T)}{T}.$$
--   3. If those coordinates are integrable under every $D_t$ of the run, then for every $\varepsilon>0$ there is $T_0\ge1$ such that, for all $T\ge T_0$, $\bar D_T$ solves the EVI for $h(x,\cdot)$ to tolerance $\varepsilon$:
--      $$\mathbb E_{p\sim\bar D_T}\big[h(x,p)^\top(y-p)\big]\le\varepsilon\qquad\text{for every }y\in Y.$$
--
--   This is the converse to the mission's goal. EVI solving is necessary as well as sufficient for online multicalibration, and the reduction is black-box: the solver is the uniform mixture of the forecaster's own outputs on a best-response run. It is a companion theorem and is not used in the proof of Theorem 4.
--
--   Differences from the source:
--   - reading: an H-multicalibrated forecaster's guarantee holds "for any h ∈ H and arbitrary sequence {(x_t, y_t)}" → the guarantee holds against adaptive Nature, which chooses x_t from the history and y_t after seeing D_t; reason: Definition 1's protocol reveals y_t after D_t ("regardless of Nature's choices"), and the source's own best-response outcomes depend on D_t
--   - generalization: the forecaster's bound holds on every sequence and every T → the bound is assumed only for T ≥ 1 and only on runs where the payoffs of h are integrable under the actual laws; reason: this is a weaker hypothesis, and every forecaster satisfying the source's hypothesis satisfies it
--   - reading: "A can be black-box converted into an efficient algorithm for solving EVIs over H" → the explicit construction of §2.1.1: on a best-response run at (x, h), the uniform mixture of D_1, …, D_T solves the EVI for h(x,·) to tolerance B(T)/T for every T ≥ 1, hence to every ε > 0 for all large T; no running time is stated; reason: the paper gives no computational model or time bound, and §2.1.1 is the theorem's only formal content
--   - encoding: MC-Err_T is o(T) → a real function B of the horizon with B(T)/T → 0; reason: the same condition
--   - encoding: y_t := argmax_{ŷ∈Y} ŷᵀ E[h(x, p_t)] → every best-response selection (any tie-breaking, any dependence on the history), plus a clause asserting that one exists; reason: the argmax may not be unique, and the existence clause shows the conclusion is not vacuous
--   - encoding: expectations are well defined → integrability of the coordinates of h(x,·) under the run's actual laws D_t, as a hypothesis of clauses 2 and 3; integrability under the mixture is concluded, not assumed; reason: the source's best response uses E_{p_t∼D_t}[h(x, p_t)], which needs these integrals; no global measurability of the tests is imposed
--   - encoding: forecaster and Nature as algorithms → a state machine (initial state, prediction, update) run by recursion against Nature's history-dependent choices, rounds numbered from 1; reason: every deterministic, or fixed-random-tape, forecaster in the protocol of Definition 1 has this form
--   - encoding: vectors in ℝ^d, tests on X × Y, laws on Y → Fin d coordinates, curried tests, Borel probability measures on the subtype Y; reason: Lean representation; forecasts range over the full Y
-- source:
--   Gabriele Farina, Juan Perdomo, An Efficient Black-Box Reduction from Online Learning to Multicalibration, and a New Route to Φ-Regret Minimization, STOC 2027 submission #721 (October 2026), Theorem 2 (Informal), second bullet, p. 7; formal statement and argument §2.1.1, pp. 13–14; Definition 1, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf. PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

import Mathlib
import Definitions.Def_MulticalibrationGGM_Reduction_Model
import Definitions.Def_MulticalibrationGGM_Reduction_Supplement_Forecaster

open MeasureTheory Filter Topology
open scoped NNReal

namespace MulticalibrationGGM.Reduction.Supplement

/-- Farina and Perdomo, STOC 2027 submission #721 (October 2026), Theorem 2 (Informal),
second bullet, p. 7, with its formal statement and argument in §2.1.1, pp. 13–14
(Multicalibration → EVI).
https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/721.pdf
PDF SHA256: 299cdd3237dbe89568ae8f4a701914eb73339a79fee7d6e00d20cd603b38af44.

Let `F` be `H`-multicalibrated against adaptive Nature with signed error bound `B`,
`B T / T → 0`. Fix a context `x` and a test `h ∈ H`. Then (i) a best-response Nature at
`(x, h)` exists; and for every best-response Nature `N` at `(x, h)`, on its run with `F`:
(ii) for every `T ≥ 1` (when the coordinates of `h(x,·)` are integrable under `D_1, …, D_T`)
the uniform mixture `D̄_T` of `D_1, …, D_T` satisfies, for every `y ∈ Y`,
`E_{p∼D̄_T}[h(x,p)ᵀ(y − p)] ≤ B T / T` with the integrand integrable; and (iii) (when those
coordinates are integrable under every `D_t`) for every `ε > 0` the mixture `D̄_T` solves the
EVI for `h(x,·)` to tolerance `ε` for all large `T`. -/
theorem theorem_2_converse {X S : Type*} {d : ℕ} (Y : Set (Vector d))
    (hYcompact : IsCompact Y) (hYconvex : Convex ℝ Y)
    (H : Set (Test X Y)) (hHbounded : BoundedTests H)
    (F : Forecaster X Y S) (B : ℕ → ℝ)
    (hB : Tendsto (fun T : ℕ => B T / (T : ℝ)) atTop (𝓝 0))
    (hF : IsMulticalibratedWithBound F H B)
    (x : X) (h : Test X Y) (hh : h ∈ H) :
    (∃ N : ForecastNature X Y, IsBestResponseNature h x N) ∧
    ∀ N : ForecastNature X Y, IsBestResponseNature h x N →
      (∀ (T : ℕ) (hT : 1 ≤ T),
        (∀ t ∈ Finset.Icc 1 T, ∀ i : Fin d,
          Integrable (fun p : Y => h x p i) ((forecastRound F N t).forecast : Measure Y)) →
        ∀ y : Y,
          Integrable (payoff h x y)
            ((uniformMixture (fun t => (forecastRound F N t).forecast) T hT : ProbabilityMeasure Y) :
              Measure Y) ∧
          expectedPayoff h x (uniformMixture (fun t => (forecastRound F N t).forecast) T hT) y ≤
            B T / (T : ℝ)) ∧
      ((∀ t : ℕ, 1 ≤ t → ∀ i : Fin d,
          Integrable (fun p : Y => h x p i) ((forecastRound F N t).forecast : Measure Y)) →
        ∀ ε : ℝ≥0, 0 < ε → ∃ T₀ : ℕ, ∃ hT₀ : 1 ≤ T₀, ∀ (T : ℕ) (hT : T₀ ≤ T),
          SolvesEVI (h x) (uniformMixture (fun t => (forecastRound F N t).forecast) T
            (hT₀.trans hT)) ε) := by sorry

end MulticalibrationGGM.Reduction.Supplement
