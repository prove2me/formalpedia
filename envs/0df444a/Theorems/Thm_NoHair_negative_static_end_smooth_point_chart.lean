-- Prove2me | Theorems.Thm_NoHair_negative_static_end_smooth_point_chart
-- name    : NoHair.negative_static_end_smooth_point_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:51:02.216798+00:00
-- url     : https://prove2.me/theorems/18cadf9c-7cc3-496b-be92-90bd7d9cbb2b
-- title:
--   Smooth positive point compactification of the negative static end
-- statement:
--   In a suitable asymptotic gauge the negative conformal metric has a smooth nondegenerate filling at its single infinity. Construct only its local punctured-ball chart, with both directions tending to the correct ends and with its metric agreeing with the pullback. Positivity of the leading lapse monopole and static asymptotic regularity are needed. Standard inversion already gives the verified upper bound.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.negative_static_end_smooth_point_chart (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (hbound : HasStaticMinusInversionBound N h) :
    Nonempty (StaticMinusPointChart Ω N h) := by sorry
