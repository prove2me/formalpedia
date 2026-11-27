-- Prove2me | Theorems.Thm_MultiNashRepair_proposition_4_6_iterations
-- name    : MultiNashRepair.proposition_4_6_iterations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:57:54.162918+00:00
-- url     : https://prove2.me/theorems/2146f9f8-e738-4441-b146-945baf09cf6c
-- title:
--   Proposition 4.6 (i) — the number of iterations of Algorithm 1 is bounded in terms of $\sigma$ only
-- statement:
--   **Proposition 4.6 (i): bounded iterations of Algorithm 1.**
--
--   Fix a rational target $\sigma$ with $1<\sigma<\sigma_\star$ and admissible controls for $\sigma$ (reserve $d$, activation fraction $f_0$, step sizes $u,\eta$, cutoff $m_0$). There is a constant $N_0$, depending only on $\sigma$ and the controls, with the following property. For every number of players $m\ge m_0$, every game with nonempty action sets and payoffs in $[0,1]$, and every run of Algorithm 1 (IDRH), whatever choices it makes (optimal LP solutions, optimal duals, best responses), every iteration index $k$ the run reaches satisfies
--   $$k\le N_0 .$$
--
--   The algorithm therefore stops after a number of iterations that depends on $\sigma$ alone, uniformly in $m$ and in the game. Together with the polynomial cost of one iteration, this gives the running time $B^{O_\sigma(1)}$ of Proposition 4.6.
--
--   **Formalization Note.** This is the first conjunct of the milestone `MultiNashRepair.proposition_4_6`; the second conjunct (the Turing-machine implementation) is `MultiNashRepair.proposition_4_6_machine`.
-- source:
--   Tang, Ding, Fang, Breaking the One-Player Extension Barrier, arXiv:2611.06076, Proposition 4.6 (part (i)), p.14; proof §5.6, pp.43–45

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH

open NashAmplification.Filtering (Utility BoundedGame)

namespace MultiNashRepair

theorem proposition_4_6_iterations (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar)
    (ctrl : Controls σ) :
    ∃ N0 : ℕ, ∀ (m : ℕ) (n : Fin m → ℕ) (u : Utility n), ctrl.m0 ≤ m → (∀ i, 0 < n i) →
      BoundedGame u → ∀ (k : ℕ) (s : State n), Reach ctrl u k s → k ≤ N0 := by sorry

end MultiNashRepair
