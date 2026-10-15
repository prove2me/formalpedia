-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_potMax_isNash
-- name    : NetworkQuality.PotentialMax.potMax_isNash
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:58.871674+00:00
-- url     : https://prove2.me/theorems/7f93bb2b-6bf3-444b-bb74-5af8cad343a6
-- title:
--   §3.5, p. 14 — every potential maximizer is a Nash equilibrium of the stage-2 subgame
-- statement:
--   In the network market under the standing assumptions, let $p,q\in\mathbb R$ and let $B\subseteq N$ maximize the potential $\Phi(\cdot,p,q)$ over all buyer sets:
--   $$\Phi(B',p,q)\le\Phi(B,p,q)\qquad\text{for every }B'\subseteq N.$$
--   Then $B$ is a (pure-strategy) Nash equilibrium of the stage-2 subgame at $(p,q)$: no buyer gains by not buying and no non-buyer gains by buying.
--
--   This is the statement that potential maximization refines Nash equilibrium in this game, which licenses using the potential maximizer as the predicted stage-2 outcome.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 14, §3.5, paragraph after (11)

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem potMax_isNash {n : ℕ} (M : Market n) (hM : M.Standing) (B : Finset (Fin n)) (p q : ℝ)
    (hB : M.IsPotMax B p q) : M.IsNash B p q := by sorry

end NetworkQuality.PotentialMax
