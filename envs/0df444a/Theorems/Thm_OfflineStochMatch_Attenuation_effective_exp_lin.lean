-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_effective_exp_lin
-- name    : OfflineStochMatch.Attenuation.effective_exp_lin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:54.961322+00:00
-- url     : https://prove2.me/theorems/766305dc-0e9c-4d66-844f-0d51aff09c7d
-- title:
--   Definition 4, p. 9 — the exponential and linear attenuation functions with α = 1/2 are effective
-- statement:
--   Let $\tilde a_{\exp}(z) = e^{-z/2}$ and $\tilde a_{\mathrm{lin}}(z) = 1 - z/2$ be the exponential and linear attenuation functions of Definition 4 with $\alpha = 1/2$. Both are effective in the sense of Definition 3: each maps $[0,1]$ into $[0,1]$, takes the value $1$ at $0$, and for every $x \in (0,1)$ the function
--   $$z \longmapsto \ln\bigl(1 - x z \tilde a(z)\bigr)$$
--   is convex on $[0,1]$.
--
--   Effectiveness is the hypothesis of Lemma 3, and it is what lets the analysis of Theorem 1 apply to these two functions.
--
--   **Formalization Note** The paper claims effectiveness for all $\alpha \ge 1/2$ and for the third function of Definition 4. The statement is made for $\alpha = 1/2$, the value Theorem 1 uses. The third function is left out because the claim is false for it: with $g(z) = \ln(1 - x z \tilde a(z))$ one finds $g''(0) = x\bigl(2(e-2)/(e-1) - x\bigr) < 0$ for $x$ close to $1$. For the linear function and $\alpha > 1$ the range condition fails, which is another reason to fix $\alpha = 1/2$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 9, Definition 4 and the sentence after it (with Definition 3, p. 8)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem effective_exp_lin :
    IsEffective (expAtt (1 / 2)) ∧ IsEffective (linAtt (1 / 2)) := by sorry

end OfflineStochMatch.Attenuation
