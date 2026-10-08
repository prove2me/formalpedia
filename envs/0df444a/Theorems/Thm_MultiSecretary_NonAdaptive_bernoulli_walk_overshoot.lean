-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_bernoulli_walk_overshoot
-- name    : MultiSecretary.NonAdaptive.bernoulli_walk_overshoot
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:26:14.408274+00:00
-- url     : https://prove2.me/theorems/f54175e0-c438-4030-8a94-47b0756ed255
-- title:
--   Lemma 5 — E[(±Nₙ − Υςₙ)₊] ≥ β₁ςₙ − (2 + 3√2) and E[(Nₙ + Υςₙ)₊²] ≤ β₂ςₙ² for centred Bernoulli sums
-- statement:
--   Let $B_1,\dots,B_n$ be independent Bernoulli variables with success probabilities $q_1,\dots,q_n\in[0,1]$, let $N_n=\sum_{t\in[n]}(B_t-q_t)$ and $\varsigma_n^2=\operatorname{Var}[N_n]=\sum_tq_t(1-q_t)$. For every $\Upsilon>0$ there are constants $\beta_1=\beta_1(\Upsilon)>0$ and $\beta_2=\beta_2(\Upsilon)$, not depending on $n$ or on the $q_t$, such that
--   $$\mathbb E[(N_n-\Upsilon\varsigma_n)_+]\ge\beta_1\varsigma_n-(2+3\sqrt2),\qquad \mathbb E[(-N_n-\Upsilon\varsigma_n)_+]\ge\beta_1\varsigma_n-(2+3\sqrt2),$$
--   and
--   $$\mathbb E\big[(N_n+\Upsilon\varsigma_n)_+^2\big]\le\beta_2\varsigma_n^2.$$
--
--   A centred Bernoulli walk overshoots any fixed multiple of its standard deviation by an amount of order $\varsigma_n$, uniformly over the success probabilities. In the proof of Theorem 3 this forces a non-adaptive policy either to run out of budget early or to leave budget unused, each by order $\sqrt n$.
--
--   **Formalization Note** The law of $(B_t)$ is the product weight $\prod_t(q_t\text{ if }b_t=1\text{ else }1-q_t)$ on $\{0,1\}^n$. $\beta_1>0$ is required: with $\beta_1=0$ the lower bounds would be trivial. Both constants are chosen before $n$ and $q$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 5, eqs. (34)–(35), p. 26

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 5 (p. 26): for every `Υ > 0` there are constants `β₁ > 0` and `β₂`, depending only on `Υ`,
such that for independent Bernoulli(`q_t`) variables, `N = ∑ (B_t - q_t)`, `ς² = ∑ q_t(1 - q_t)`:
`E[(N - Υς)_+] ≥ β₁ς - (2 + 3√2)`, `E[(-N - Υς)_+] ≥ β₁ς - (2 + 3√2)` (34) and
`E[((N + Υς)_+)²] ≤ β₂ς²` (35). -/
theorem bernoulli_walk_overshoot (Υ : ℝ) (hΥ : 0 < Υ) :
    ∃ β₁ β₂ : ℝ, 0 < β₁ ∧
      ∀ (n : ℕ) (q : Fin n → ℝ), (∀ t, q t ∈ Set.Icc (0 : ℝ) 1) →
        β₁ * Real.sqrt (varSum q) - (2 + 3 * Real.sqrt 2) ≤
            ∑ b, bernWeight q b * max (centeredSum q b - Υ * Real.sqrt (varSum q)) 0 ∧
        β₁ * Real.sqrt (varSum q) - (2 + 3 * Real.sqrt 2) ≤
            ∑ b, bernWeight q b * max (-centeredSum q b - Υ * Real.sqrt (varSum q)) 0 ∧
        ∑ b, bernWeight q b * (max (centeredSum q b + Υ * Real.sqrt (varSum q)) 0) ^ 2 ≤
            β₂ * Real.sqrt (varSum q) ^ 2 := by sorry

end MultiSecretary.NonAdaptive
