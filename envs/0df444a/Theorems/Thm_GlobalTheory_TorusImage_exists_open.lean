-- Prove2me | Theorems.Thm_GlobalTheory_TorusImage_exists_open
-- name    : GlobalTheory.TorusImage.exists_open
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:48:01.209908+00:00
-- url     : https://prove2.me/theorems/b2dedb8e-f2b2-55d1-94df-e7468c06205d
-- title:
--   Torus Image: exists open
-- statement:
--   The Torus Image construction uses the exists open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L187-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusImageFactorQuotientGoodOpen.lean#L187-L231

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

theorem GlobalTheory.TorusImage.exists_open (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : SmConn G)
    [IrreducibleSpace G.left] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp k) X ⟶ G) (hi : IsMonHom i) :
    ∃ U : G.left.Opens, (U : Set G.left).Nonempty ∧ ∀ (Y : Over (Sp k)) (t : Y ⟶ splitTorus (Sp k) X) (g : Y ⟶ G),
      (∀ χ ∈ weights i, SplitTorus.val t χ = 1) → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ U → ⊤ ≤ g.left ⁻¹ᵁ U →
      (t ≫ i) * g = g := by sorry
