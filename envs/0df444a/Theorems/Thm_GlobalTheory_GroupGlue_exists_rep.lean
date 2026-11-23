-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_exists_rep
-- name    : GlobalTheory.GroupGlue.exists_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:39.496799+00:00
-- url     : https://prove2.me/theorems/911f38ee-f1a4-4779-a9ba-b355c0cd1b40
-- title:
--   Group Glue: exists rep
-- statement:
--   The Group Glue construction uses the exists rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L176-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L176-L178

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
variable [∀ i, GrpObj (H i)]
omit [∀ i, GrpObj (H i)]

theorem GlobalTheory.GroupGlue.exists_rep (hψ : ∀ i, IsPullback (ψ i) (H i).hom G.hom (𝒰.f i)) {i : 𝒰.I₀} {S : Scheme.{0}}
    {u : S ⟶ 𝒰.X i} {T : Over X} {g : S ⟶ T.left} (h : u ≫ 𝒰.f i = g ≫ T.hom) (x : T ⟶ G) :
    ∃ a : Over.mk u ⟶ H i, a.left ≫ ψ i = g ≫ x.left := by sorry
