-- Prove2me | Theorems.Thm_GenPayoffSG_Solvable_theorem_4_9
-- name    : GenPayoffSG.Solvable.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:52.977694+00:00
-- url     : https://prove2.me/theorems/65c7f337-3472-415b-b101-d62dbec92b64
-- title:
--   Theorem 4.9, p. 16 — in every stochastic game, for every ε > 0, some subgame Γ_h admits an ε-equilibrium
-- statement:
--   Let $\Gamma=(I,S,(A_i)_{i\in I},p,(f_i)_{i\in I})$ be a stochastic game: finitely many players, finitely or countably many states, finite action sets, and bounded Borel-measurable payoff functions on runs. Then for every $\varepsilon>0$ there is an **$\varepsilon$-solvable subgame**: there are a history $h\in H$ and a strategy profile $\sigma$ such that
--   $$\mathbf E_{h,\sigma}[f_i]\ \ge\ \mathbf E_{h,\sigma_i',\sigma_{-i}}[f_i]-\varepsilon\qquad\text{for every player }i\text{ and every strategy }\sigma_i'.$$
--
--   The subgame may depend on $\varepsilon$. Whether every such game has an $\varepsilon$-equilibrium from a given initial state is a long-standing open problem; Theorem 4.9 shows that at least some subgame always has one. For shift-invariant payoffs it gives an initial state with an $\varepsilon$-equilibrium (Corollary 4.10).
--
--   **Formalization Note** The history $h$ ranges over the paper's $H$ (feasible histories, from any initial state); the $\varepsilon$-equilibrium is for the subgame $\Gamma_h$, whose expected payoffs are $\mathbf E_{h,\cdot}[f_i]$, and deviations range over all strategies. Lean index $n$ is paper stage $n+1$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, p. 16, Theorem 4.9 (with Definition 4.8)

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_Game

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem theorem_4_9 (G : Game I S A) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (h : Hist I S A n), Feasible G h ∧ IsEpsSolvable G ε n h := by sorry

end GenPayoffSG.Solvable
