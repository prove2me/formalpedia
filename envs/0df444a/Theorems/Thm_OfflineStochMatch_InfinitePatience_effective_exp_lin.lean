-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_effective_exp_lin
-- name    : OfflineStochMatch.InfinitePatience.effective_exp_lin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:08.445438+00:00
-- url     : https://prove2.me/theorems/dca3ee9e-82a5-4aaa-9682-8086a1bd542b
-- title:
--   p. 9, after Definition 4 — the exponential and linear attenuation functions with α = 1/2 are effective
-- statement:
--   Let $\tilde a_{\exp}(z)=e^{-z/2}$ and $\tilde a_{\rm lin}(z)=1-z/2$ be the exponential and linear attenuation functions of Definition 4 with $\alpha=1/2$. Both are *effective* in the sense of Definition 3: each maps $[0,1]$ into $[0,1]$, takes the value $1$ at $0$, and for every $x\in(0,1)$
--   $$z\longmapsto \ln\bigl(1-xz\,\tilde a(z)\bigr)\quad\text{is convex on }[0,1].$$
--
--   Effectiveness is the hypothesis of Lemma 3, through which the paper bounds the probability that an edge is safe; it is what makes these two functions usable in Corollary 5.
--
--   **Formalization Note.** The paper claims effectiveness for all $\alpha\ge 1/2$ and also for the third function of Definition 4. The statement here is the case $\alpha=1/2$, the value the algorithm uses; the claim for all $\alpha\ge 1/2$ is false as printed (the linear function leaves $[0,1]$ for $\alpha>1$, and numerically the convexity fails for the exponential function at $\alpha=2$). The third function is excluded because the claim is false for it: with $g(z)=\ln(1-xz\tilde a(z))$ one finds $g''(0)=x\bigl(2(e-2)/(e-1)-x\bigr)<0$ for $x\in(0.836,1)$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 9, sentence after Definition 4 (with Definition 3, p. 8)

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- p. 9, after Definition 4: the exponential and the linear attenuation functions with `α = 1/2`
are effective (Definition 3). -/
theorem effective_exp_lin : IsEffective (expAtt (1 / 2)) ∧ IsEffective (linAtt (1 / 2)) := by sorry

end OfflineStochMatch.InfinitePatience
