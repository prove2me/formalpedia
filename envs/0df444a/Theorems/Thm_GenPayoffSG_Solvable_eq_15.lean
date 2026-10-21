-- Prove2me | Theorems.Thm_GenPayoffSG_Solvable_eq_15
-- name    : GenPayoffSG.Solvable.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:23.306002+00:00
-- url     : https://prove2.me/theorems/5c11b3c3-3a2b-4700-90e3-b586dcb7e4e3
-- title:
--   Eq. (15), p. 20 — under σ*, Y^n_i = D^δ_i(r^n) is a submartingale
-- statement:
--   Let $\Gamma$ be a stochastic game and $\delta>0$. For each player $i$ let $D^\delta_i$ be a Martin function for $\delta$ and $i$ (Theorem 3.1, minmax version), and let $\sigma^*$ be a strategy profile such that $\sigma^*(h)$ is an equilibrium of the one-shot game $G_O(D^\delta,h)$ for every history $h\in H$ (as in Theorem 4.4). Fix an initial state $s$ and a player $i$, and define $Y^n_i(r)=D^\delta_i(r^n)$. Then $(Y^n_i)_{n\in\mathbb N}$ is a submartingale under $\mathbf P_{\sigma^*}=\mathbf P_{s,\sigma^*}$ with respect to $(\mathcal F^n)_n$:
--   $$\mathbf E_{\sigma^*}\big[Y^{n+1}_i\mid\mathcal F^n\big]\ \ge\ Y^n_i\qquad\forall n\in\mathbb N.\tag{15}$$
--
--   The proof of Theorem 4.9 uses (15) to make the minmax values almost constant along the play, which is what makes punishment effective in the subgame it constructs.
--
--   **Formalization Note** Mathlib's `Submartingale` also contains adaptedness and integrability of every $Y^n_i$; both are part of the claim. The process is $n\mapsto D_i(n,\ \text{frestrictLe } n\ r)$, the paper's $Y^{n+1}_i$ (Lean index $n$ is paper stage $n+1$), and the filtration is `Filtration.piLE`.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, p. 20, §4.4 Step 2, definition of Y^n_i and Eq. (15)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_OneShot

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem eq_15 (G : Game I S A) (δ : ℝ) (hδ : 0 < δ) (D : I → HistFun I S A)
    (hD : ∀ i, IsMartinFunction G δ i (D i))
    (x : (n : ℕ) → Hist I S A n → ∀ j, PMF (A j))
    (hx : ∀ n (h : Hist I S A n), Feasible G h → IsOneShotEquilibrium G D h (x n h))
    (s : S) (i : I) :
    Submartingale (fun n r => D i n (Preorder.frestrictLe n r)) Filtration.piLE
      (playMeasure G (fun j n h => x n h j) 0 (initHist s)) := by sorry

end GenPayoffSG.Solvable
