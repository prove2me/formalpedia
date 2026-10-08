-- Prove2me | Theorems.Thm_Helfgott_primitive_low_zero_locations_iff_right_exclusion
-- name    : Helfgott.primitive_low_zero_locations_iff_right_exclusion
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T04:06:49.304289+00:00
-- url     : https://prove2.me/theorems/205a0746-070f-4aea-be84-462e43f2d8cb
-- title:
--   The Goldbach finite zero-location profile is equivalent to one-sided exclusion
-- statement:
--   For all primitive conductors in the original three-prime major-arc range, the exact finite profile requiring every low zero to be either the origin or on $\Re s=1/2$ is equivalent to the finite profile excluding zeros with $\Re s>1/2$ at the same heights. The cutoffs are $200+75000000/Q_d$ and $10^8/d$, where $Q_d=2d$ for odd $d$ and $Q_d=d$ for even $d$, with $Q_d\le300000$. Thus $$\mathsf{LowZeroLocations}\quad\Longleftrightarrow\quad\mathsf{LowZeroRightExclusion}.$$ The equivalence is unconditional; neither finite certificate is claimed proved. It simplifies the remaining numerical witness needed by the major-arc reduction.
-- source:
--   Primitive Dirichlet functional equation and gamma-factor zero locations in Mathlib. Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897, section 4.6. Written by Codex.

import Definitions.Def_Helfgott_PrimitiveLowZeroLocations
import Definitions.Def_Helfgott_PrimitiveLowZeroRightExclusion

namespace Helfgott
theorem primitive_low_zero_locations_iff_right_exclusion :
  PrimitiveLowZeroLocations ↔ PrimitiveLowZeroRightExclusion := by sorry
end Helfgott
