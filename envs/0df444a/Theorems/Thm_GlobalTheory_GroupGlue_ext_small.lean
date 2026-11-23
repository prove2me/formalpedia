-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_ext_small
-- name    : GlobalTheory.GroupGlue.ext_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:44.712444+00:00
-- url     : https://prove2.me/theorems/9829f05e-ce69-4611-949b-ac19034dc5e4
-- title:
--   Group Glue: ext small
-- statement:
--   The Group Glue construction uses the ext small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L16-L20

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

theorem GlobalTheory.GroupGlue.ext_small {T Y : Scheme.{0}} (t : T ⟶ X) {p q : T ⟶ Y}
    (h : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → g ≫ p = g ≫ q) :
    p = q := by sorry
