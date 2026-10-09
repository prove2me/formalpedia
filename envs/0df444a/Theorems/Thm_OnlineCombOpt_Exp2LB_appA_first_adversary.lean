-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2LB_appA_first_adversary
-- name    : OnlineCombOpt.Exp2LB.appA_first_adversary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:56.21998+00:00
-- url     : https://prove2.me/theorems/9e7fc680-8ec6-4e7d-be58-678b19e45871
-- title:
--   App. A, p. 15 — against the alternating adversary, EXP2 has regret exactly (nd/16) tanh(ηd/8)
-- statement:
--   Let $d$ be a multiple of $4$, let $n$ be even, and let $\eta\in\mathbb R$. Let $\mathcal A_d\subseteq\{0,1\}^d$ be the action set of App. A ($d/4$ ones among the first $d/2$ coordinates, together with exactly one of the intervals $\{d/2+1,\dots,d/2+d/4\}$ and $\{d/2+d/4+1,\dots,d\}$). Consider the alternating adversary
--   $$z_t(i)=\begin{cases}1 & i\in\{d/2+1,\dots,d/2+d/4\},\ t\text{ odd},\\ 1 & i\in\{d/2+d/4+1,\dots,d\},\ t\text{ even},\\ 0&\text{otherwise.}\end{cases}$$
--   Then the regret of full-information EXP2 with learning rate $\eta$ on $\mathcal A_d$ against this adversary over $n$ rounds is
--   $$R_n=\frac{nd}{16}\tanh\Bigl(\frac{\eta d}{8}\Bigr).$$
--
--   This is the first of the two lower bounds combined in the proof of Theorem 1: it is large when $\eta$ is large.
--
--   **Formalization Note** "$d$ a multiple of $4$ and $n$ even" are the standing assumptions of App. A (p. 14). The identity is stated for every real $\eta$ (the paper uses $\eta\ge 0$); it is also true at $d=0$, where $\mathcal A_0=\{0\}$ and both sides vanish, so $d>0$ is not assumed. Rounds are 0-based in Lean, so the paper's odd rounds are the even indices of `adv1`.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, App. A, p. 15, the first adversary and the display "R_n = nd/16 + … = (nd/16) tanh(ηd/8)"

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

namespace OnlineCombOpt.Exp2LB

/-- App. A, p. 15 (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2): against the alternating adversary
`adv1 d`, full-information EXP2 with learning rate `η` on the action set `thmOneSet d` has regret
exactly `R_n = (nd/16) tanh(ηd/8)`, when `d` is a multiple of 4 and `n` is even. -/
theorem appA_first_adversary (d n : ℕ) (η : ℝ) (hd : 4 ∣ d) (hn : Even n) :
    exp2Regret (thmOneSet d) η (adv1 d) n = (n : ℝ) * d / 16 * Real.tanh (η * d / 8) := by sorry

end OnlineCombOpt.Exp2LB
