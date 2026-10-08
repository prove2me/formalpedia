-- Prove2me | Theorems.Thm_ManneLP_Equilibrium_terminal_law_eq_7
-- name    : ManneLP.Equilibrium.terminal_law_eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:09:22.122828+00:00
-- url     : https://prove2.me/theorems/2c089901-2db3-4338-8c1f-6fdda8710aac
-- title:
--   §4, (6)–(7) — the law of the terminal stock in terms of the joint probabilities xᵢⱼ
-- statement:
--   Consider Manne's inventory model with stock levels $0,\dots,T$, admissible pairs $A$ and demand law $(p_n)$. Let $q(j\mid i)$ be any assignment of production probabilities and $y=(y_0,\dots,y_T)$ any weights on the initial stock, and put $x_{ij}=y_i\,q(j\mid i)$. If the chain of $q$ moves from $i$ to $t$ with probability $P_q(i,t)=\sum_{j}q(j\mid i)\Pr(\max(0,i+j-n)=t)$, then the law $y'_t=\sum_i y_iP_q(i,t)$ of the terminal stock is given by (7):
--   $$
--   y'_0=\sum_{\substack{i,j,n:\\ i+j-n\le 0}}p_nx_{ij},\qquad
--   y'_t=\sum_{\substack{i,j,n:\\ i+j-n=t}}p_nx_{ij}\quad(t=1,2,\dots,T).
--   $$
--
--   This identifies the right-hand sides of the equilibrium equations (8.0)–(8.T) with the one-step law of the controlled Markov chain, which is the link between the decision problem and the linear program.
--
--   **Formalization Note** The identity holds for every $q$ and $y$, with no normalization, and is stated that way. Sums over $(i,j)$ run over the admissible pairs; sums over $n$ are `tsum`s.
-- source:
--   Manne, Linear Programming and Sequential Decisions, Management Science 6 (1960), pp. 261–262 (PDF pp. 4–5), §4, (6) and (7)

import Mathlib
import Definitions.Def_ManneLP_Equilibrium_Model
import Definitions.Def_ManneLP_Equilibrium_Chain
import Definitions.Def_ManneLP_Equilibrium_LP

namespace ManneLP.Equilibrium

theorem terminal_law_eq_7 (M : Model) (q : ℕ → ℕ → ℝ) (y : ℕ → ℝ) :
    ∑ i ∈ states M, y i * trans M q i 0 = rhsZero M (jointLaw y q) ∧
    ∀ t : ℕ, 1 ≤ t → t ≤ M.T →
      ∑ i ∈ states M, y i * trans M q i t = rhsPos M (jointLaw y q) t := by sorry

end ManneLP.Equilibrium
