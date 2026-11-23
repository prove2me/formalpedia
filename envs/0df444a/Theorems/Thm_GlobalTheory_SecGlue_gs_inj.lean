-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_gs_inj
-- name    : GlobalTheory.SecGlue.gs_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:32.075858+00:00
-- url     : https://prove2.me/theorems/7db36584-9efe-446b-8c94-4204d67687ed
-- title:
--   Sec Glue: gs inj
-- statement:
--   The Sec Glue construction uses the gs inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L29-L33

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
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.SecGlue.gs_inj (r : Z ⟶ X) [IsOpenImmersion r] (z : Z) {U V : X.Opens} (h : r z ∈ U) (h' : r z ∈ V)
    {a : Γ(X, U)} {b : Γ(X, V)} (e : gs r z U a = gs r z V b) :
    gs (𝟙 X) (r z) U a = gs (𝟙 X) (r z) V b := by sorry
