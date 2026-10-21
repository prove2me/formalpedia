-- Prove2me | Theorems.Thm_GenPayoffSG_Solvable_eq_19
-- name    : GenPayoffSG.Solvable.eq_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:48.737371+00:00
-- url     : https://prove2.me/theorems/7729a089-3985-4a86-8457-1cb4f08ec27b
-- title:
--   Eq. (19), p. 21 — Lévy's zero-one law: an event of positive P_σ-probability has P_{h*,σ}-probability > 1 − δ at some history h* past stage n_0
-- statement:
--   Let $\Gamma$ be a stochastic game, $\sigma$ a strategy profile, $s$ an initial state, and $B$ a measurable set of runs with $\mathbf P_{s,\sigma}(B)>0$. Then for every $\delta>0$ and every stage $n_0$ there are a stage $n^*\ge n_0$ and a history $h^*\in H$ in stage $n^*$ with $\mathbf P_{s,\sigma}(C(h^*))>0$ and
--   $$\mathbf P_{h^*,\sigma}(B)\ >\ 1-\delta.\tag{19}$$
--
--   In the proof of Theorem 4.9 this is applied to $\sigma=\sigma^*$ and $B=\widehat{\mathscr R}_{n_0}$ of (18), the set of runs on which the payoffs, the minmax values and their conditional expectations have settled to within $\delta$; the subgame $\Gamma_{h^*}$ is the one shown to be $\varepsilon$-solvable.
--
--   **Formalization Note** The paper states the conclusion for the specific set $\widehat{\mathscr R}_{n_0}$ and attributes it to Lévy's zero-one law; the Lean statement is that law's consequence for an arbitrary measurable $B$ of positive probability. The conjunct $\mathbf P_{s,\sigma}(C(h^*))>0$ is added: Lévy's law yields it, the paper leaves it implicit, and the proof uses it on p. 23 when it transfers almost-sure statements under $\mathbf P_{\sigma^*}$ to $\mathbf P_{h^*,\sigma^*}$; without it $h^*$ could be a null history. The probability $\mathbf P_{h^*,\sigma}(B)$ is compared with $1-\delta$ as a real number (`toReal` of a probability). Lean index $n$ is paper stage $n+1$, which preserves "$n^*\ge n_0$" for every $n_0$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, p. 21, §4.4 Step 2, Eq. (19) (with P_σ*(R̂_{n0}) > 0)

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_Game

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem eq_19 (G : Game I S A) (σ : Profile G) (s : S) (B : Set (Run I S A))
    (hB : MeasurableSet B) (hpos : 0 < playMeasure G σ 0 (initHist s) B)
    (δ : ℝ) (hδ : 0 < δ) (n₀ : ℕ) :
    ∃ n, n₀ ≤ n ∧ ∃ h : Hist I S A n, Feasible G h ∧
      0 < playMeasure G σ 0 (initHist s) (cylinder h) ∧
      1 - δ < (playMeasure G σ n h B).toReal := by sorry

end GenPayoffSG.Solvable
