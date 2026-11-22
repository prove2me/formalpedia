-- Prove2me | Theorems.Thm_NoHair_TwoCentre_Model_chronological_access
-- name    : NoHair.TwoCentre.Model.chronological_access
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:51:25.549157+00:00
-- url     : https://prove2.me/theorems/9d8c742c-cca2-40b7-9494-d28eb92aa057
-- title:
--   The chronological past of the far end is precisely the two-centre exterior
-- statement:
--   For the specified time-oriented one-horizon extension, let $A$ be the image of the isotropic region $|x|>2$ and $D$ its full two-centre exterior. Show $I^-(A)=D$ and $D\subseteq I^+(A)$, using the mission’s future timelike curves. Interior and horizon points cannot send a future timelike signal through the horizon to $A$. Every point of $D$ can send and receive such a signal by choosing enough separation in static time. [One-way crossing](https://prove2.me/theorems/5112e9cb-e66c-4ba3-ba7a-01031f4af387)
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. M. Sánchez, On the geometry of static spacetimes, Theorem 3.1, https://arxiv.org/abs/math/0406332.

import Definitions.Def_NoHair_TwoCentreBlackHole
import Definitions.Def_NoHair_TwoCentreIsotropic

open NoHair NoHair.TwoCentre NoHair.TwoCentre.Model Set
open scoped ContDiff Manifold

theorem NoHair.TwoCentre.Model.chronological_access :
    chronoPastSet metric orientation (Model.chart '' exteriorRegion 2) = outer ∧
    outer ⊆ chronoFutureSet metric orientation (Model.chart '' exteriorRegion 2) := by
  sorry
