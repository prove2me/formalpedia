-- Prove2me | Theorems.Thm_GlobalTheory_SS_WeakNeronDef_fromSpecStalk_comp
-- name    : GlobalTheory.SS.WeakNeronDef.fromSpecStalk_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:58.956093+00:00
-- url     : https://prove2.me/theorems/19db3c9c-8248-433c-bf2c-9fa340de8a79
-- title:
--   Weak Neron Def: from Spec Stalk comp
-- statement:
--   The Weak Neron Def construction uses the from Spec Stalk comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsModelMapDefinedWeakNeronFamily.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsModelMapDefinedWeakNeronFamily.lean#L20-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsModelMapDefinedWeakNeronFamily
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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronDef

theorem GlobalTheory.SS.WeakNeronDef.fromSpecStalk_comp {X : Scheme.{0}} {B : CommRingCat.{0}} (p : X ⟶ Spec B) (x : X) :
    X.fromSpecStalk x ≫ p =
      Spec.map ((Scheme.ΓSpecIso B).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ x trivial) := by sorry
