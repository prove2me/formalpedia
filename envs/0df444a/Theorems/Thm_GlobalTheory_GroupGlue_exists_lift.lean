-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_exists_lift
-- name    : GlobalTheory.GroupGlue.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:11:58.688073+00:00
-- url     : https://prove2.me/theorems/e5346f2f-be59-4a41-9f0f-762ac14f90e0
-- title:
--   Group Glue: exists lift
-- statement:
--   The Group Glue construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L53-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}

theorem GlobalTheory.GroupGlue.exists_lift (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) (i : 𝒰.I₀) {S : Scheme.{0}}
    (u : S ⟶ 𝒰.X i) (x : S ⟶ G.left) (h : u ≫ 𝒰.f i = x ≫ G.hom) :
    ∃ a : Over.mk u ⟶ H i, a.left ≫ ψ i = x := by sorry
