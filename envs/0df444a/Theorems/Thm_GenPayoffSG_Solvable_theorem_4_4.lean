-- Prove2me | Theorems.Thm_GenPayoffSG_Solvable_theorem_4_4
-- name    : GenPayoffSG.Solvable.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:22:28.02068+00:00
-- url     : https://prove2.me/theorems/eaeceee5-c084-4ae1-a44f-bb733cc93e74
-- title:
--   Theorem 4.4, pp. 11–12 — equilibria of the one-shot games G_O(D^ε, h) form a minmax ε-acceptable profile; such a profile exists
-- statement:
--   Let $\Gamma$ be a stochastic game and $\varepsilon>0$. For each player $i$ let $D^\varepsilon_i$ be a Martin function for $\varepsilon$ and $i$ (Theorem 3.1, minmax version), and put $D^\varepsilon=(D^\varepsilon_i)_{i\in I}$. For each history $h\in H$ let $x(h)\in\prod_{i\in I}\Delta(A_i)$ be an equilibrium of the one-shot game $G_O(D^\varepsilon,h)$, and define the strategy profile $\sigma^*$ by $\sigma^*(h)=x(h)$. Then $\sigma^*$ is minmax $\varepsilon$-acceptable:
--   $$\mathbf E_{h,\sigma^*}[f_i]\ \ge\ \overline v_i(h)-\varepsilon\qquad\text{for every player }i\text{ and every history }h\in H.$$
--   Consequently, in every stochastic game and for every $\varepsilon>0$ there exists a minmax $\varepsilon$-acceptable strategy profile.
--
--   The profile $\sigma^*$ is the starting point of the proof of Theorem 4.9, where it is used with a small parameter $\delta$ in place of $\varepsilon$.
--
--   **Formalization Note** The statement is the conjunction of the two sentences. The family $x$ is a function of all finite sequences; the equilibrium property is required at the feasible histories $h\in H$ only. "Equilibrium in $G_O(D^\varepsilon,h)$" is `AGT.IsMixedNash` for the $|I|$-player finite game with payoffs $a\mapsto\mathbf E[D^\varepsilon_j\mid h,a]$, with the mixed actions given as the real weights of the PMFs $x(h)_j$. Lean index $n$ is paper stage $n+1$.
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, pp. 11–12, Theorem 4.4 (with Definition 4.3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_GenPayoffSG_Solvable_OneShot

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

theorem theorem_4_4 (G : Game I S A) (ε : ℝ) (hε : 0 < ε) :
    (∀ D : I → HistFun I S A, (∀ i, IsMartinFunction G ε i (D i)) →
      ∀ x : (n : ℕ) → Hist I S A n → ∀ j, PMF (A j),
        (∀ n (h : Hist I S A n), Feasible G h → IsOneShotEquilibrium G D h (x n h)) →
        IsMinmaxAcceptable G ε (fun j n h => x n h j)) ∧
    ∃ σ : Profile G, IsMinmaxAcceptable G ε σ := by sorry

end GenPayoffSG.Solvable
