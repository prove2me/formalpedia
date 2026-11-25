-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_exists_oAct
-- name    : GlobalTheory.GroupGlue.exists_oAct
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:57:40.436282+00:00
-- url     : https://prove2.me/theorems/26f03f72-6708-41d0-aab2-3e31f0dc7b1a
-- title:
--   Group Glue: exists o Act
-- statement:
--   The Group Glue construction uses the exists o Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L270-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L270-L318

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

theorem GlobalTheory.GroupGlue.exists_oAct {O : Type} [CommRing O] (h : ∀ i, IsGrpPullback (H i) G (𝒰.f i) (ψ i)) (α : ∀ i, OAct O (H i))
    (he : ∀ (x : O) (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a : Over.mk u ⟶ H i)
      (b : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j →
        (a ≫ (α i).act x).left ≫ ψ i = (b ≫ (α j).act x).left ≫ ψ j) :
    ∃ A : OAct O G, ∀ x i, ((α i).act x).left ≫ ψ i = ψ i ≫ (A.act x).left := by sorry
