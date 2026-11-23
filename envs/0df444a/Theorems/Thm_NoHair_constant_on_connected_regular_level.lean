-- Prove2me | Theorems.Thm_NoHair_constant_on_connected_regular_level
-- name    : NoHair.constant_on_connected_regular_level
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T09:16:45.827842+00:00
-- url     : https://prove2.me/theorems/b6ae224a-54e7-4df6-a0ce-74b3afda3b01
-- title:
--   Constancy on a connected regular level surface
-- statement:
--   Suppose $S\subset\mathbb R^3$ is connected and agrees locally with the regular zero set of a $C^1$ function $N$. A differentiable function whose derivative vanishes on $S$ is constant on $S$. A local inverse function chart flattens the level surface; constancy on convex pieces of the coordinate plane implies the global assertion.
-- source:
--   Inverse function theorem and the mean value theorem on convex sets, as used for constancy of the surface gravity of a connected regular static horizon in P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

theorem NoHair.constant_on_connected_regular_level (W S : Set ADMPoint) (N f : ADMPoint → ℝ)
    (hs : IsConnected S) (hw : IsOpen W) (hsub : S ⊆ W)
    (hN : ContDiffOn ℝ 1 N W) (hf : DifferentiableOn ℝ f W)
    (hreg : ∀ x ∈ S, fderiv ℝ N x ≠ 0)
    (hlevel : ∀ x ∈ S, ∀ᶠ y in 𝓝 x, y ∈ S ↔ N y = 0)
    (hzero : ∀ x ∈ S, fderiv ℝ f x = 0) : ∀ x ∈ S, ∀ y ∈ S, f x = f y := by sorry
