-- Prove2me | Theorems.Thm_NoHair_scalar_flat_zero_mass_rigidity_three
-- name    : NoHair.scalar_flat_zero_mass_rigidity_three
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T08:07:09.177544+00:00
-- url     : https://prove2.me/theorems/949fc724-bcde-4a0c-9025-9b17690c5f2b
-- title:
--   Positive-mass rigidity for a scalar-flat one-ended three-manifold
-- statement:
--   Let a connected, complete, smooth Riemannian three-manifold without boundary be scalar flat and have one asymptotically flat end. In end coordinates $h-\delta=O(r^{-1})$ with the corresponding decay through two derivatives. Suppose its ADM mass is zero. Then it is globally isometric to Euclidean three-space, by a smooth isometry with smooth inverse pulling back the Euclidean inner product to $h$. The metric distance is required to be the Riemannian distance.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Theorem 5.2 (p. 22 of the preprint) and its use after (5.6) on p. 24, https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. The scalar-flat one-ended case is used here. The metric falloff is (2.1) with exponent one and two derivatives.

import Definitions.Def_NoHair_riemannianMassRigidity

open NoHair Set Filter InnerProductSpace
open scoped Manifold ContDiff Topology

theorem NoHair.scalar_flat_zero_mass_rigidity_three : ThreeDimensionalZeroMassRigidity := by sorry
