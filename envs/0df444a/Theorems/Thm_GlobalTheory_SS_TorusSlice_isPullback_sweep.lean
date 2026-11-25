-- Prove2me | Theorems.Thm_GlobalTheory_SS_TorusSlice_isPullback_sweep
-- name    : GlobalTheory.SS.TorusSlice.isPullback_sweep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:29:05.30542+00:00
-- url     : https://prove2.me/theorems/9cb849d8-476d-5c65-bbea-0b935ca057b3
-- title:
--   Torus Slice: is Pullback sweep
-- statement:
--   The Torus Slice construction uses the is Pullback sweep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L64-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L64-L102

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

theorem GlobalTheory.SS.TorusSlice.isPullback_sweep {T G Y Y₁ W : Over S} [GrpObj T] [GrpObj G] (i : T ⟶ G) [IsMonHom i] (j : Y ⟶ G) [Mono j]
    (σ : Y ⟶ T) (hσ : Equivar i j σ) (e : Y₁ ⟶ Y) (he : IsPullback e (toUnit Y₁) σ η[T])
    (p : W ⟶ T ⊗ Y) (r : W ⟶ Y) (hW : IsPullback p r (((snd T Y ≫ σ)⁻¹ ≫ i) * (snd T Y ≫ j)) j) :
    ∃ q, IsPullback q p ((fst T Y₁ ≫ i) * (snd T Y₁ ≫ e ≫ j)) ((fst T Y ≫ i) * (snd T Y ≫ j)) := by sorry
