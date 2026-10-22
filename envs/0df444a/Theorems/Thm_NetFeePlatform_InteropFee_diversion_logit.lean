-- Prove2me | Theorems.Thm_NetFeePlatform_InteropFee_diversion_logit
-- name    : NetFeePlatform.InteropFee.diversion_logit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:19.678815+00:00
-- url     : https://prove2.me/theorems/e3fbe874-618e-4859-8449-c4d2597ae66c
-- title:
--   (32), p. 39 — the Logit diversion ratio is Σ_{k≠j} e^{−tᵏ}/(e^z + Σ_{k≠j} e^{−tᵏ}), independent of tʲ, and equals Σ_{k≠j}∂nᵏ/∂tʲ over −∂nʲ/∂tʲ
-- statement:
--   Consider $J$ platforms with Logit demand $n^k(t) = e^{-t^k}/(w + \sum_{i} e^{-t^i})$, outside-option weight $w = e^{z} \ge 0$, and assume that $w > 0$ or $J \ge 2$. Fix a platform $j$ and a net-fee profile $t$. Then the diversion ratio $\varphi^j(t) = \sum_{k \ne j} n^k(t)/(1 - n^j(t))$ satisfies:
--
--   1. the closed form
--   $$\varphi^j(t) = \frac{\sum_{k\ne j} e^{-t^k}}{w + \sum_{k \ne j} e^{-t^k}},$$
--   which does not involve $t^j$;
--   2. the defining property of the diversion ratio (p. 25): as a function of platform $j$'s own net fee $s$, with the other fees fixed, the total rival demand $\sum_{k\ne j} n^k$ has derivative at $s = t^j$
--   $$\sum_{k\ne j} \frac{\partial n^k}{\partial t^j} = \varphi^j(t)\,\Big(-\frac{\partial n^j}{\partial t^j}\Big) = \varphi^j(t)\, n^j(t)\big(1 - n^j(t)\big).$$
--
--   Independence from $t^j$ is what makes the condition $\partial\varphi^j/\partial t^j \le 0$ of Appendix E.1.3 automatic under Logit demand, so that the first-order condition characterizes best responses.
--
--   **Formalization Note** The Logit own-fee derivative $-\partial n^j/\partial t^j = n^j(1-n^j)$ is used to write the right-hand side of part 2. The hypothesis "$w > 0$ or $J \ge 2$" rules out the degenerate single platform without outside option, where $1 - n^j = 0$.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 39, Appendix C.2, (32); p. 25, definition of the diversion ratio φʲ(t)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropFee
theorem diversion_logit {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (t : Fin J → ℝ) (j : Fin J) :
    NetFeePlatform.Competition.diversion w t j = (∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) /
        (w + ∑ k ∈ Finset.univ.erase j, Real.exp (-t k)) ∧
      HasDerivAt (fun s => ∑ k ∈ Finset.univ.erase j, NetFeePlatform.Competition.demand w (Function.update t j s) k)
        (NetFeePlatform.Competition.diversion w t j * (NetFeePlatform.Competition.demand w t j * (1 - NetFeePlatform.Competition.demand w t j))) (t j) := by sorry
end NetFeePlatform.InteropFee
