-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_theorem_5_5_1
-- name    : MDPFinance.BayesianModels.theorem_5_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:20.136927+00:00
-- url     : https://prove2.me/theorems/561bc1a4-093f-4b62-a82f-848e65ed66a0
-- title:
--   Theorem 5.5.1 — the two-unknown-arms bandit's optimal index policy
-- statement:
--   **Theorem 5.5.1.** In the two-unknown-arms Bernoulli bandit (Section 5.5), with
--   $d_n := p_2 + \beta Q_2 J_{n-1} - p_1 - \beta Q_1 J_{n-1}$:
--
--   a) The policy $\pi^* = (f_N^*,\dots,f_1^*)$ is optimal, where $f_n^*(x) = 2$ if $d_n(x) \ge 0$,
--   $1$ if $d_n(x) < 0$ — the *largest* maximizer of $J_{n-1}$'s one-step problem.
--
--   b) $(d_n)$ satisfies the recursion $d_1 = p_2 - p_1$, $d_{n+1} = (1-\beta)d_1 + \beta Q_2 d_n^+ -
--   \beta Q_1 d_n^-$.
--
--   c) When $\beta = 1$, the **stay-on-a-winner** property holds: $f_{n+1}^*(x) = a \Rightarrow
--   f_n^*(x + e_{2a-1}) = a$ — if it is optimal to play arm $a$ and it succeeds, it remains optimal to
--   play arm $a$ again.
--
--   This is the finite-horizon analogue of the Gittins-index theory for this book's own two-armed
--   bandit (the *infinite*-horizon case is chunk `07c`'s Theorem 7.6.10): here, with a finite horizon,
--   the optimal policy is an explicit, computable index rule built directly from the one-step
--   Bellman advantage $d_n$, rather than from a retirement-value/index construction.
--
--   **Formalization Note.** $f^*$ is defined directly by the explicit tie-breaking rule (arm 2 on a
--   tie), which *is* the "largest maximizer" the book refers to — no separate abstract maximizer
--   condition is needed. The stay-on-a-winner property (c) and the recursion (b) are independent
--   conjuncts about the same explicitly-constructed $f^*$.
--
--   **Moderation note.** Part c) is stated for $n\ge 1$: the draft's clause at $n=0$ compared $f^*_1$ with `f 0`, which is not a decision rule of the policy (the draft's `hf` makes it constantly arm 2), and was refutable whenever $d_1(x)<0$. Optimality in a) now also states $V^\pi_N\le J_N$ for every Markov policy.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 168, Theorem 5.5.1

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_TwoArmBandit

open MeasureTheory

namespace MDPFinance.BayesianModels

/-- Theorem 5.5.1 (Bäuerle–Rieder, p. 168, PDF 181). Let `d_n := p_2 + β Q_2 J_{n-1} - p_1 -
β Q_1 J_{n-1}` for `n ∈ ℕ`. Then it holds: a) The policy `π^* = (f_N^*,\dots,f_1^*)` is optimal,
where `f_n^*(x) = 2` if `d_n(x) ≥ 0`, `1` if `d_n(x) < 0`, is the largest maximizer of
`J_{n-1}`. b) The sequence `(d_n)` satisfies the recursion `d_1 = p_2 - p_1`,
`d_{n+1} = (1-β) d_1 + β Q_2 d_n^+ - β Q_1 d_n^-`. c) Let `β = 1`. Then the "stay-on-a-winner"
property holds for the optimal policy `π^*`, i.e. `f_{n+1}^*(x) = a ⇒ f_n^*(x + e_{2a-1}) = a`
(the arm-1 and arm-2 cases of `a` stated as separate conjuncts, arms coded `0`/`1` for `1`/`2`
respectively), for `n ∈ ℕ`, i.e. `n ≥ 1` (`f_0^*` is not a decision rule of the policy).
Optimality in a) is stated as `V^{π^*}_N = J_N` together with `V^π_N ≤ J_N` for every Markov
policy `π`. -/
theorem theorem_5_5_1 (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (N : ℕ)
    (f : ℕ → BanditState2 → Fin 2)
    (hf : ∀ n x, f n x = if 0 ≤ dB β n x then (1 : Fin 2) else 0) :
    (∀ x, VpiB β f N x = JB β N x) ∧
      (∀ (g : ℕ → BanditState2 → Fin 2) (x : BanditState2), VpiB β g N x ≤ JB β N x) ∧
      (dB β 1 = fun x => p2B x - p1B x) ∧
      (∀ n ≥ 1, dB β (n + 1) = fun x => (1 - β) * dB β 1 x +
        β * Q2B (fun y => max (dB β n y) 0) x - β * Q1B (fun y => max (-dB β n y) 0) x) ∧
      (β = 1 → ∀ n, 1 ≤ n → ∀ x,
        (f (n + 1) x = 0 → f n (badd x bE1) = 0) ∧
          (f (n + 1) x = 1 → f n (badd x bE3) = 1)) := by sorry

end MDPFinance.BayesianModels
