-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Rel_gs_eq
-- name    : GlobalTheory.SecGlue.Rel.gs_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:22.071493+00:00
-- url     : https://prove2.me/theorems/cc7693c8-8a19-4919-8825-eb7e6c69fa4e
-- title:
--   Rel: gs eq
-- statement:
--   The Rel construction uses the gs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L97-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}

theorem GlobalTheory.SecGlue.Rel.gs_eq {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q')
    {s : LB.Sec (LB.LinComb L (fun _ : K => q) ε)} {t : LB.Sec (LB.LinComb L (fun _ : K => q') ε)}
    (H : Rel h s t) (j : K → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : K => q') j) :
    gs (r ≫ h) z (LB.wchart L (fun _ : K => q) j) (s.f j) =
      gs r z (LB.wchart L (fun _ : K => q') j) (t.f j) := by sorry
