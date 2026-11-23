-- Prove2me | Theorems.Thm_NoHair_negative_static_end_inversion_bound
-- name    : NoHair.negative_static_end_inversion_bound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:51:10.593649+00:00
-- url     : https://prove2.me/theorems/dc361ebb-3227-426e-8e6e-5be69cb3d9ec
-- title:
--   Uniform upper bound for the negative conformal metric in inversion coordinates
-- statement:
--   The negative conformal metric is bounded above by $C|x|^{-4}$ times the Euclidean metric far out. Pulling back by unit inversion gives a uniform metric upper bound on the punctured ball about the proposed added point. Smoothness and positive definiteness at that point require additional information.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.negative_static_end_inversion_bound (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    HasStaticMinusInversionBound N h := by sorry
