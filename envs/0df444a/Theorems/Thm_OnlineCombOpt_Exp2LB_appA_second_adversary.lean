-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2LB_appA_second_adversary
-- name    : OnlineCombOpt.Exp2LB.appA_second_adversary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:56.114149+00:00
-- url     : https://prove2.me/theorems/a1bb46ce-4b2a-4881-b25f-81eaee31d379
-- title:
--   App. A, p. 16 — against the constant adversary with ε = min(log 2/(ηn), 1), EXP2 has regret ≥ min(d log 2/(12η), nd/12)
-- statement:
--   Let $d$ be a multiple of $4$, let $n\ge 1$, and let $\eta>0$. Put $\varepsilon=\min\bigl(\log 2/(\eta n),\,1\bigr)\in(0,1]$ and consider the constant adversary
--   $$z_t(i)=\begin{cases}1-\varepsilon & i\le d/4,\\ 1 & i\in\{d/4+1,\dots,d/2\},\\ 0&\text{otherwise,}\end{cases}\qquad t=1,\dots,n.$$
--   Then the regret of full-information EXP2 with learning rate $\eta$ on the action set $\mathcal A_d$ of App. A against this adversary over $n$ rounds satisfies
--   $$R_n\;\ge\;\min\Bigl(\frac{d\log 2}{12\eta},\ \frac{nd}{12}\Bigr).$$
--
--   This is the second of the two lower bounds combined in the proof of Theorem 1: it is large when $\eta$ is small. Its proof uses Lemma 3.
--
--   **Formalization Note** $\log$ is the natural logarithm. The hypotheses $\eta>0$ and $n\ge1$ make $\log 2/(\eta n)$ and $d\log 2/(12\eta)$ the paper's quantities (in Lean, $x/0=0$). The parity of $n$ is not used by this adversary and is not assumed. The bound also holds at $d=0$ (both sides are $0$), so $d>0$ is not assumed.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, App. A, p. 15 (the second adversary) and p. 16 (last display before Appendix B)

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

namespace OnlineCombOpt.Exp2LB

/-- App. A, p. 16, last display (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2): against the constant
adversary `adv2 d ε` with `ε = min(log 2/(ηn), 1)`, full-information EXP2 with learning rate
`η > 0` on the action set `thmOneSet d` has regret `R_n ≥ min(d log 2/(12η), nd/12)`, when `d` is
a multiple of 4 and `n ≥ 1`. -/
theorem appA_second_adversary (d n : ℕ) (η : ℝ) (hd : 4 ∣ d) (hn : 0 < n) (hη : 0 < η) :
    min ((d : ℝ) * Real.log 2 / (12 * η)) ((n : ℝ) * d / 12) ≤
      exp2Regret (thmOneSet d) η (adv2 d (min (Real.log 2 / (η * n)) 1)) n := by sorry

end OnlineCombOpt.Exp2LB
