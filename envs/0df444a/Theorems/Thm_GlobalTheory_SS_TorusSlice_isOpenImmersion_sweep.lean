-- Prove2me | Theorems.Thm_GlobalTheory_SS_TorusSlice_isOpenImmersion_sweep
-- name    : GlobalTheory.SS.TorusSlice.isOpenImmersion_sweep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:20:43.213207+00:00
-- url     : https://prove2.me/theorems/8ea39061-be7d-453f-88b3-97d6d990f6b5
-- title:
--   Torus Slice: is Open Immersion sweep
-- statement:
--   The Torus Slice construction uses the is Open Immersion sweep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L104-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L104-L132

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

theorem GlobalTheory.SS.TorusSlice.isOpenImmersion_sweep {T G Y Y₁ : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G)
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    [Flat T.hom] [LocallyOfFinitePresentation T.hom] [QuasiCompact T.hom] [IsOpenImmersion j.left] [QuasiCompact j.left] :
    IsOpenImmersion ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)).left := by sorry
