-- Prove2me | Theorems.Thm_NoHair_ksRadius_superlevel_frontier
-- name    : NoHair.ksRadius_superlevel_frontier
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:11.619604+00:00
-- url     : https://prove2.me/theorems/31c42fe2-1d74-4c32-8e59-050876e4749c
-- title:
--   Boundary and connectedness of positive Kerr–Schild radial levels
-- statement:
--   Let $a$ be any rotation parameter and $b>0$. Take boundaries in the open manifold $U_a=\{r>0\}$. The boundary of the superlevel set and the topology of its radial level satisfy
--
--   $$\partial_{U_a}\{r>b\}=\{r=b\},\qquad \{r=b\}\text{ is nonempty and connected}.$$
--
--   At each fixed time the level is the ellipsoid with equatorial semiaxis $\sqrt{b^2+a^2}$ and polar semiaxis $b$. Taking $b=r_+$ supplies the topological part of the connected-horizon assertion independently of the mass and charge.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, https://arxiv.org/abs/1410.6626v2, §3.1, Eqs. (3.11)–(3.15) and the implicit equation for the oblate radial coordinate immediately after Eq. (3.15).

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.ksRadius_superlevel_frontier (a b : ℝ) (hb : 0 < b) :
    frontier {x : kerrNewmanSpacetime a | b < ksRadius a x.val} =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = b} ∧
      IsConnected {x : kerrNewmanSpacetime a | ksRadius a x.val = b} := by sorry
