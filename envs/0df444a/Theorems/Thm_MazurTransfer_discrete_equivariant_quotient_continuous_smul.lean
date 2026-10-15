-- Prove2me | Theorems.Thm_MazurTransfer_discrete_equivariant_quotient_continuous_smul
-- name    : MazurTransfer.discrete_equivariant_quotient_continuous_smul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-14T23:32:46.795565+00:00
-- url     : https://prove2.me/theorems/c6c1c4fc-98aa-463b-9567-a433dfc5f674
-- title:
--   Continuous actions descend along equivariant surjections to discrete coefficients
-- statement:
--   Let G be a topological group acting continuously on a space X, and acting on a discrete space Y. A continuous surjective G-equivariant function X to Y makes the action on Y continuous. Stabilizers in Y are open because every point has a lift and its orbit map is continuous. This supplies the genuine topology on actual norm-character quotient coefficients before forming their continuous Galois H1 and Kummer restriction maps.
-- source:
--   Owned MazurTheorem integration, Apache-2.0. Extracted from ContinuousCoefficientExponentAndContinuity.quotient_continuousSMul. Checked at default limits on Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Topology.Algebra.MulAction

theorem MazurTransfer.discrete_equivariant_quotient_continuous_smul
    (G X Y : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction G X] [TopologicalSpace X] [ContinuousSMul G X]
    [MulAction G Y] [TopologicalSpace Y] [DiscreteTopology Y]
    (f : X → Y) (hf : Continuous f) (hs : Function.Surjective f)
    (he : ∀ (g : G) (x : X), f (g • x) = g • f x) : ContinuousSMul G Y := by sorry
