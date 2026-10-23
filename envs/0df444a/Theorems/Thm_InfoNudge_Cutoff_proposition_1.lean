-- Prove2me | Theorems.Thm_InfoNudge_Cutoff_proposition_1
-- name    : InfoNudge.Cutoff.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:48.575558+00:00
-- url     : https://prove2.me/theorems/ce476c57-1e84-477c-8c2b-d3f25231d163
-- title:
--   Proposition 1, p. 16 — if (15) holds, the unconstrained-optimal mechanism 1{θ ≤ tʰ} is an optimal incentive-compatible mechanism
-- statement:
--   Under the standing assumptions and Assumption 1 ($P[\theta\le t^h]>0$ and $P[\theta>t^a]>0$), suppose that
--   $$E[\theta\mid\theta>t^h]\ge t^a.\qquad(15)$$
--   Then the unconstrained-optimal mechanism $\pi^*_{\gamma^u}(\theta)=1_{\{\theta\le t^h\}}$ (with $\gamma^u=F(t^h)$) is incentive-compatible, and its objective $t^hE[\pi(\theta)]-E[\theta\pi(\theta)]$ is at least that of every incentive-compatible mechanism $\pi$.
--
--   In this case the designer can avoid harmful consumption altogether: consumption is recommended exactly to the types for which the date-0 self finds it beneficial.
--
--   **Formalization Note** The paper says "the optimal" mechanism; the optimum is not unique (it can be modified on $P$-null sets), so the statement asserts that $1_{\{\theta\le t^h\}}$ is *an* optimal mechanism. Condition (15) is stored as $t^aP[\theta>t^h]\le E[\theta1_{\{\theta>t^h\}}]$, which is equivalent because $P[\theta>t^h]\ge P[\theta>t^a]>0$.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), p. 16, Proposition 1, condition (15)

import Mathlib
import Definitions.Def_InfoNudge_Cutoff_Model

namespace InfoNudge.Cutoff

theorem proposition_1 (M : Params) (hS : Standing M) (hA : Assumption1 M) (h15 : Cond15 M) :
    IsOptimal M (Set.indicator (Set.Iic (th M)) (fun _ => (1 : ℝ))) := by sorry

end InfoNudge.Cutoff
