-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyPresentation_coboundaries_continuous
-- name    : MazurTransfer.ContinuousFirstCohomologyPresentation.coboundaries_continuous
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T23:30:28.807255+00:00
-- url     : https://prove2.me/theorems/47c17201-69f7-4630-a888-c2ee3011d9b2
-- title:
--   Algebraic first coboundaries are continuous for a continuous action
-- statement:
--   Let G act continuously by automorphisms on an abelian topological group M. Every algebraic first coboundary $$z(g)=g\cdot m/m$$ is continuous. The topology on G need not be a group topology in this statement. This identifies algebraic coboundaries among the continuous cocycles used in the original continuous first-cohomology presentation.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologyPresentation.coboundaries_continuous, with complete original type and proof retained. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous H1 is continuous 1-cocycles modulo
1-coboundaries, presented inside Mathlib algebraic group cohomology.
The forgetful map is checked injective; comparison to Mathlib homological
continuous cohomology is a separate boundary. Named downstream consumer:
the actual norm Kummer injection and the local Selmer conditions.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyPresentationData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation

theorem MazurTransfer.ContinuousFirstCohomologyPresentation.coboundaries_continuous (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] [ContinuousSMul G M] (z : G → Additive M)
    (hz : z ∈ groupCohomology.coboundaries₁ (rep G M)) :
    Continuous (fun g : G => (Additive.toMul (z g) : M)) := by sorry
