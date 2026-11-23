-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_rep_mul
-- name    : GlobalTheory.GroupGlue.rep_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:48.175445+00:00
-- url     : https://prove2.me/theorems/2474aef7-01ef-4958-be60-dff2d6e8e325
-- title:
--   Group Glue: rep mul
-- statement:
--   The Group Glue construction uses the rep mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L248-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L248-L256

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
variable [GrpObj G]

theorem GlobalTheory.GroupGlue.rep_mul (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) {i : 𝒰.I₀} {S : Scheme.{0}} {u : S ⟶ 𝒰.X i}
    {a b : Over.mk u ⟶ H i} {T : Over X} {x y : T ⟶ G} {g : S ⟶ T.left} (hg : u ≫ 𝒰.f i = g ≫ T.hom)
    (ha : a.left ≫ ψ i = g ≫ x.left) (hb : b.left ≫ ψ i = g ≫ y.left) :
    (a * b).left ≫ ψ i = g ≫ (x * y).left := by sorry
