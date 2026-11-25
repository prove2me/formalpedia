-- Prove2me | Theorems.Thm_GlobalTheory_TorusImage_exists_finset_ext
-- name    : GlobalTheory.TorusImage.exists_finset_ext
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:42:04.216003+00:00
-- url     : https://prove2.me/theorems/1a49aa6b-f86e-4109-8a63-235bfa979f6b
-- title:
--   Torus Image: exists finset ext
-- statement:
--   The Torus Image construction uses the exists finset ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L43-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L43-L65

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

theorem GlobalTheory.TorusImage.exists_finset_ext {S : Scheme.{0}} [IsAffine S] (G : Over S) [LocallyOfFiniteType G.hom] {U : G.left.Opens}
    (hU : IsAffineOpen U) : ∃ s : Finset Γ(G.left, U), ∀ (Z : Over S) (g g' : Z ⟶ G) (h : ⊤ ≤ g.left ⁻¹ᵁ U)
      (h' : ⊤ ≤ g'.left ⁻¹ᵁ U), (∀ f ∈ s, (g.left.appLE U ⊤ h).hom f = (g'.left.appLE U ⊤ h').hom f) → g = g' := by sorry
