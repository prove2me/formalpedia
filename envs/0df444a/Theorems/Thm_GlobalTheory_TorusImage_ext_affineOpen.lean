-- Prove2me | Theorems.Thm_GlobalTheory_TorusImage_ext_affineOpen
-- name    : GlobalTheory.TorusImage.ext_affineOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:51:48.361791+00:00
-- url     : https://prove2.me/theorems/00cdaa50-1f02-5693-891a-58a75c8428d0
-- title:
--   Torus Image: ext affine Open
-- statement:
--   The Torus Image construction uses the ext affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L32-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
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
open GlobalTheory GlobalTheory.TorusImage

theorem GlobalTheory.TorusImage.ext_affineOpen {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ g ⁻¹ᵁ U) (h' : ⊤ ≤ g' ⁻¹ᵁ U) (e : g.appLE U ⊤ h = g'.appLE U ⊤ h') : g = g' := by sorry
