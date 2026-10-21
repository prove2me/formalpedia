-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_logit_deriv
-- name    : NetFeePlatform.Competition.logit_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:23.939593+00:00
-- url     : https://prove2.me/theorems/be87fc92-9ff0-4100-bb57-f2fe637ca4b6
-- title:
--   §3.1, Example: Logit Demand, p. 13 — under (13), ∂nʲ/∂tʲ = −nʲ(1 − nʲ)
-- statement:
--   Let $J$ platforms charge net fees $t=(t^1,\dots,t^J)$ and let demand take the Logit form with outside-option weight $w\ge0$,
--   $$n^j(t)=\frac{e^{-t^j}}{w+\sum_k e^{-t^k}}.$$
--   Then, holding the other platforms' net fees fixed, platform $j$'s share is differentiable in its own net fee, with
--   $$\frac{\partial n^j(t)}{\partial t^j}=-\,n^j(t)\,\big(1-n^j(t)\big).$$
--
--   This identity turns the general pricing formula of Proposition 1 into the explicit Logit formula (14), and is the basic computation behind every equilibrium characterization of the paper's §5–6.
--
--   **Formalization Note** The derivative is stated as `HasDerivAt` of $s\mapsto n^j(t^j{=}s,t^{-j})$ at $s=t^j$. The weight $w=e^{z}$ is allowed to be $0$ (no outside option).
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 13, §3.1, Example: Logit Demand, after (13)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.Competition
theorem logit_deriv {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (t : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun s => demand w (Function.update t j s) j)
      (-(demand w t j * (1 - demand w t j))) (t j) := by sorry
end NetFeePlatform.Competition
