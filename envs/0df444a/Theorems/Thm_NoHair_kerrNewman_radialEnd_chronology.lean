-- Prove2me | Theorems.Thm_NoHair_kerrNewman_radialEnd_chronology
-- name    : NoHair.kerrNewman_radialEnd_chronology
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T19:45:09.990071+00:00
-- url     : https://prove2.me/theorems/2f1eb1cc-08a2-43d4-bdd9-126d3d367c89
-- title:
--   Chronological reach of large radial ends in ingoing Kerr–Newman spacetime
-- statement:
--   Suppose $m>0$ and $a^2+e^2\le m^2$. On the positive-radius Kerr–Schild spacetime there exists a continuous timelike orientation $T$ with the following property for every $R>r_++|a|$. Writing $A_R=\{\rho>R\}$ for the spatial end and $D=\{r>r_+\}$ for the radial exterior, one has
--
--   $$I^-(A_R)=D,\qquad D\subseteq I^+(A_R).$$
--
--   Thus every exterior point can send a timelike signal to the end and receive one from it. No point on or inside the outer horizon can send such a signal to this end. One orientation works for all the cutoffs, including in the extremal case $r_+=m$.
-- source:
--   T. Adamo and E. T. Newman, The Kerr–Newman metric: A Review, https://arxiv.org/abs/1410.6626v2, §3.3, Eqs. (3.18)–(3.21) and the ensuing discussion of the future horizon and extremality; Prove2Me, NoHair.kerrNewman_isStationaryBlackHole, https://prove2.me/theorems/d4aa60f2-99c7-4a52-9c28-6ba24b2ddbac, domain of outer communications in the positive-radius ingoing patch.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open NoHair Set

theorem NoHair.kerrNewman_radialEnd_chronology (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    ∃ T : VecField (kerrNewmanSpacetime a), IsTimeOrientation (kerrNewmanMetricField m a e) T ∧
      ∀ R : ℝ, kerrNewmanOuterRadius m a e + |a| < R →
        let A := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
        let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
        chronoPastSet (kerrNewmanMetricField m a e) T A = D ∧
        D ⊆ chronoFutureSet (kerrNewmanMetricField m a e) T A := by sorry
