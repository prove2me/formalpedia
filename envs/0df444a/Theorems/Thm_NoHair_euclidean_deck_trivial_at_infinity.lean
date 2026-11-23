-- Prove2me | Theorems.Thm_NoHair_euclidean_deck_trivial_at_infinity
-- name    : NoHair.euclidean_deck_trivial_at_infinity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:49:38.012741+00:00
-- url     : https://prove2.me/theorems/02aa004a-e658-420c-a384-64cd0f38563f
-- title:
--   An asymptotically injective Euclidean projection has no nontrivial deck isometries
-- statement:
--   If a Euclidean projection is injective outside a bounded set, every isometry commuting with that projection fixes all points. Far points and their images lie in the injective region. Every point is the midpoint of two such fixed points.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.euclidean_deck_trivial_at_infinity {Q : Type*} (p : ADMPoint → Q) (R : ℝ) (sheet : Set.InjOn p {x | R < ‖x‖})
    (d : ADMPoint ≃ᵢ ADMPoint) (deck : ∀ z, p (d z)=p z) : ∀ x : ADMPoint, d x=x := by sorry
