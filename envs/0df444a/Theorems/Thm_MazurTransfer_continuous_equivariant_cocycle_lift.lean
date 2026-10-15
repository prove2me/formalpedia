-- Prove2me | Theorems.Thm_MazurTransfer_continuous_equivariant_cocycle_lift
-- name    : MazurTransfer.continuous_equivariant_cocycle_lift
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T23:46:24.914279+00:00
-- url     : https://prove2.me/theorems/5e97a263-cd96-4296-ae43-3c979f72b363
-- title:
--   Continuous cocycles lift through injective equivariant coefficient maps
-- statement:
--   Let G act by automorphisms on commutative groups M and N, with N discrete. Let i: M to N be an injective equivariant homomorphism. If a continuous multiplicative one-cocycle z: G to N has every value in the image of i, then z lifts to a continuous one-cocycle w: G to M satisfying i(w(g))=z(g). Injectivity proves the cocycle law, while a chosen inverse on the image extends to a continuous function on the discrete group N. This supplies the kernel-cocycle lifting step in continuous H1 exactness for the actual ordered norm-character sequences.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Extracted from ContinuousFirstCohomologyKernelLift. Checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Topology.Algebra.Group.Basic

theorem MazurTransfer.continuous_equivariant_cocycle_lift
    (G M N : Type*) [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology N]
    (i : M →* N) (hi : Function.Injective i)
    (he : ∀ (g : G) (m : M), i (g • m) = g • i m)
    (z : G → N) (hz : groupCohomology.IsMulCocycle₁ z) (hc : Continuous z)
    (hrange : ∀ g : G, ∃ m : M, i m = z g) :
    ∃ w : G → M, Continuous w ∧ groupCohomology.IsMulCocycle₁ w ∧
      ∀ g : G, i (w g) = z g := by sorry
