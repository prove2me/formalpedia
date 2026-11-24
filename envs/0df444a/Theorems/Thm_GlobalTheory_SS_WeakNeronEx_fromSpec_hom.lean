-- Prove2me | Theorems.Thm_GlobalTheory_SS_WeakNeronEx_fromSpec_hom
-- name    : GlobalTheory.SS.WeakNeronEx.fromSpec_hom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:27.463362+00:00
-- url     : https://prove2.me/theorems/5a0df646-95ed-4317-89b0-8064da663125
-- title:
--   Weak Neron Ex: from Spec hom
-- statement:
--   The Weak Neron Ex construction uses the from Spec hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L74-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.SS.WeakNeronEx.fromSpec_hom {X : Scheme.{0}} {K : Type} [CommRing K] (f : X ⟶ Sp K) {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f = spMap (cst f W) := by sorry
