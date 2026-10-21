-- Prove2me | Theorems.Thm_NetFeePlatform_InteropDominance_logit_deriv
-- name    : NetFeePlatform.InteropDominance.logit_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:21.680845+00:00
-- url     : https://prove2.me/theorems/159758e8-0cf2-45d5-85f2-96245b265c16
-- title:
--   §3.1, (13), p. 13 — the Logit own-fee derivative ∂nʲ/∂tʲ = −nʲ(1 − nʲ)
-- statement:
--   Let $J$ platforms charge net fees $t=(t^1,\dots,t^J)$, let the outside option have weight $w\ge 0$, and let $n^j(t)=e^{-t^j}/(w+\sum_k e^{-t^k})$ be Logit demand. Fix platform $j$ and the other platforms' fees. Then, as a function of its own fee, $j$'s demand is differentiable with
--
--   $$\frac{\partial n^j}{\partial t^j}=-n^j(1-n^j).$$
--
--   This identity is what turns the general pricing formula into its Logit form: the markup $n^j/(-\partial n^j/\partial t^j)$ becomes $1/(1-n^j)$.
--
--   **Formalization Note** The derivative is stated with `HasDerivAt` at the point $t^j$, varying only coordinate $j$ of the fee profile. The hypothesis $w\ge 0$ is the paper's ($w=e^{z}$, or $w=0$ with no outside option); it keeps the denominator positive.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 13, §3.1, Example: Logit Demand, (13)

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.InteropDominance

theorem logit_deriv {J : ℕ} (w : ℝ) (hw : 0 ≤ w) (t : Fin J → ℝ) (j : Fin J) :
    HasDerivAt (fun s => NetFeePlatform.Competition.demand w (Function.update t j s) j)
      (-(NetFeePlatform.Competition.demand w t j * (1 - NetFeePlatform.Competition.demand w t j))) (t j) := by sorry

end NetFeePlatform.InteropDominance
