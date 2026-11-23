-- Prove2me | Theorems.Thm_GlobalTheory_GroupGlue_exists_glue
-- name    : GlobalTheory.GroupGlue.exists_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:10.859154+00:00
-- url     : https://prove2.me/theorems/24aaad5f-1bfa-4516-8f08-bab5aa7ab7f9
-- title:
--   Group Glue: exists glue
-- statement:
--   The Group Glue construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L22-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean#L22-L49

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

theorem GlobalTheory.GroupGlue.exists_glue {T Y : Scheme.{0}} (t : T ⟶ X) (P : ∀ S : Scheme.{0}, (S ⟶ T) → (S ⟶ Y) → Prop)
    (ex : ∀ (i : 𝒰.I₀) (S : Scheme.{0}) (g : S ⟶ T) (u : S ⟶ 𝒰.X i), u ≫ 𝒰.f i = g ≫ t → ∃ z, P S g z)
    (nat : ∀ (S S' : Scheme.{0}) (k : S' ⟶ S) (g : S ⟶ T) (z : S ⟶ Y), P S g z → P S' (k ≫ g) (k ≫ z))
    (uniq : ∀ (S : Scheme.{0}) (g : S ⟶ T) (z z' : S ⟶ Y), P S g z → P S g z' → z = z') :
    ∃ z : T ⟶ Y, ∀ (S : Scheme.{0}) (g : S ⟶ T) (z' : S ⟶ Y), P S g z' → g ≫ z = z' := by sorry
