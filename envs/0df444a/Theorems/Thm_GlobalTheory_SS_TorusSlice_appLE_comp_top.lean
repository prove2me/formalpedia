-- Prove2me | Theorems.Thm_GlobalTheory_SS_TorusSlice_appLE_comp_top
-- name    : GlobalTheory.SS.TorusSlice.appLE_comp_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:29.022506+00:00
-- url     : https://prove2.me/theorems/eb21d30d-b932-4f22-947f-2fd6b321e494
-- title:
--   Torus Slice: app LE comp top
-- statement:
--   The Torus Slice construction uses the app LE comp top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L165-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L165-L171

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.TorusSlice
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X]

theorem GlobalTheory.SS.TorusSlice.appLE_comp_top {Z Y G : Over S} (y : Z ⟶ Y) (f : Y ⟶ G) (g : Z ⟶ G) (e : g = y ≫ f) (U : G.left.Opens)
    (h : ⊤ ≤ g.left ⁻¹ᵁ U) (h' : ⊤ ≤ f.left ⁻¹ᵁ U) (u : Γ(G.left, U)) :
    (g.left.appLE U ⊤ h).hom u = y.left.appTop.hom ((f.left.appLE U ⊤ h').hom u) := by sorry
