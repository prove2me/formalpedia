-- Prove2me | Theorems.Thm_GenPayoffSG_Solvable_theorem_3_1
-- name    : GenPayoffSG.Solvable.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:24.757989+00:00
-- url     : https://prove2.me/theorems/9dba66b7-2d3e-4f3f-b9b9-d446d3662d13
-- title:
--   Theorem 3.1, pp. 8–9 — for every ε > 0 and player i there is a bounded Martin function D^ε_i with properties (1)–(3)
-- statement:
--   Let $\Gamma$ be a stochastic game with finitely many players, countably many states, finite action sets and bounded Borel-measurable payoffs. Let $\varepsilon>0$ and let $i$ be a player. Then there is a bounded function $D_i^\varepsilon:H\to\mathbb R$, a **Martin function** for $\varepsilon$ and $i$, such that
--   1. $\overline v_i(h)-\varepsilon\le D^\varepsilon_i(h)\le\overline v_i(h)$ for every $h\in H$;
--   2. $D^\varepsilon_i(h)\le\overline v_{O,i}(D^\varepsilon_i,h)$ for every $h\in H$;
--   3. for every history $h'\in H$ and every strategy profile $\sigma$, if
--   $$\overline v_{O,i}(D^\varepsilon_i,h)\le\mathbf E[D^\varepsilon_i\mid h,\sigma(h)]\qquad\forall h\in H\text{ with }h'\preceq h,\tag{4}$$
--   then $\overline v_{O,i}(D^\varepsilon_i,h)\le\mathbf E_{h,\sigma}[f_i]$ for every $h\in H$ with $h'\preceq h$.
--
--   Here $\overline v_i(h)$ is player $i$'s minmax value in the subgame at $h$, and $\overline v_{O,i}(D,h)$ and $\mathbf E[D\mid h,\cdot]$ are the minmax value and the payoff of the one-shot game $G_O(D,h)$ in which player $i$ receives the expectation of $D$ at the next history. Property 3 says that a profile that is locally good for player $i$ in every one-shot game is globally good in the stochastic game.
--
--   The paper does not prove this theorem: it attributes the two-player single-state case to Martin (1998), the multiplayer single-state case to Ashkenazi-Golan, Flesch, Predtetchinski and Solan (2022a, Theorem 3.6 and Claim 3.5, with the modification of footnote 3 for the left inequality of property 1), and the extension to countable state spaces to the method of Maitra and Sudderth (1998).
--
--   **Formalization Note** Only the minmax version is stated; the theorem's last sentence (the same result with every minmax value replaced by the maxmin value) is not formalized. Every "for every $h\in H$" ranges over feasible histories (`Feasible`), and $h'\preceq h$ is `Extends h' h`. Lean index $n$ is paper stage $n+1$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, pp. 8–9, Theorem 3.1 (minmax version), Eq. (4)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_OneShot

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem theorem_3_1 (G : Game I S A) (ε : ℝ) (hε : 0 < ε) (i : I) :
    ∃ D : HistFun I S A, IsMartinFunction G ε i D := by sorry

end GenPayoffSG.Solvable
