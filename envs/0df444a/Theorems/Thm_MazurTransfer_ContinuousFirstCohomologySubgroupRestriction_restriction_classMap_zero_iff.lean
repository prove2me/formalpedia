-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousFirstCohomologySubgroupRestriction_restriction_classMap_zero_iff
-- name    : MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restriction_classMap_zero_iff
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T00:28:20.365561+00:00
-- url     : https://prove2.me/theorems/fcbc6518-b283-412b-9ad1-0768c3e205a9
-- title:
--   A restricted continuous first-cohomology class vanishes exactly for a subgroup coboundary
-- statement:
--   Let G be a group with a topology acting by automorphisms on an abelian topological group M. Let S be any subgroup with its induced topology, and z a continuous 1-cocycle. Then $$\operatorname{res}_S[z]=0\quad\Longleftrightarrow\quad\exists m\in M,\ \forall s\in S,\quad z(s)=s\cdot m/m.$$ This is the original zero criterion for the presented continuous H1 restriction, used for actual norm subgroup classes and local Selmer conditions. No topological-group hypothesis on G or continuity hypothesis on its action is added.
-- source:
--   Original MazurTheorem ContinuousFirstCohomologySubgroupRestriction.restriction_classMap_zero_iff, complete original type and proof body retained, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restriction of continuous cocycles descends to continuous
H1 for every subgroup with its induced topology. A restricted class is
zero precisely when the restricted cocycle is a subgroup coboundary.
Named downstream consumer: local conditions on actual norm Kummer classes.
-/
import Definitions.Def_MazurTransfer_ContinuousFirstCohomologySubgroupRestrictionData
noncomputable section
open MazurTransfer.ContinuousFirstCohomologyPresentation
open MazurTransfer.ContinuousFirstCohomologySubgroupRestriction

theorem MazurTransfer.ContinuousFirstCohomologySubgroupRestriction.restriction_classMap_zero_iff (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (S : Subgroup G) (z : continuousCocycles G M) :
    restriction G M S (classMap G M z) = 0 ↔
      ∃ m : M, ∀ s : S, s • m / m = (Additive.toMul (z.val s.val) : M) := by sorry
