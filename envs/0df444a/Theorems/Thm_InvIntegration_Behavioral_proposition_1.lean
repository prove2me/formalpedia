-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_proposition_1
-- name    : InvIntegration.Behavioral.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:02.50531+00:00
-- url     : https://prove2.me/theorems/f908ae80-f1e8-49d2-80de-cde141364e7d
-- title:
--   Proposition 1, p. 8 (PDF 8) — a consumer buys in period 1 iff v ≥ v∗ = min(vh, max((p − ξs)/(1 − ξδ), p))
-- statement:
--   Let consumers believe that a unit is available in period 2 with probability $\tilde\xi\in[0,1]$. A consumer with valuation $v<v_h$ buys in period 1 when the surplus $v-p$ is at least the larger of the expected waiting surplus $\tilde\xi(\delta v - s)$ and $0$ (ties go to period 1). Then
--   $$\max\bigl(\tilde\xi(\delta v-s),\,0\bigr) \le v-p \iff v \ge v^*(\tilde\xi) = \min\Bigl(v_h,\ \max\Bigl(\frac{p-\tilde\xi s}{1-\tilde\xi\delta},\ p\Bigr)\Bigr),$$
--   with $v^*(\tilde\xi)=v_h$ when $\tilde\xi\delta = 1$.
--
--   This is the threshold structure of consumer behavior: consumers with valuation at least $v^*$ buy at full price, the rest consider waiting.
--
--   **Formalization Note.** Valuations lie in $(v_l,v_h)$; the statement is proved for every $v<v_h$. The case $\tilde\xi\delta=1$ (only at $\tilde\xi=\delta=1$) is where the page's fraction is $+\infty$, and the definition of $v^*$ returns $v_h$ there.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 8 (PDF 8), Proposition 1, eq. (1)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem proposition_1 (P : Params) (hS : P.Standing) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (v : ℝ) (hv : v < P.vh) :
    max (ξ * (P.δ * v - P.s)) 0 ≤ v - P.p ↔ vstar P ξ ≤ v := by sorry

end InvIntegration.Behavioral
