-- Prove2me | Theorems.Thm_GlobalTheory_SS_TorusSlice_goodOpen_of_equivar
-- name    : GlobalTheory.SS.TorusSlice.goodOpen_of_equivar
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:21:29.364067+00:00
-- url     : https://prove2.me/theorems/e284f495-d7ac-46cb-9f6c-8829d071e2e3
-- title:
--   Torus Slice: good Open of equivar
-- statement:
--   The Torus Slice construction uses the good Open of equivar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L173-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L173-L210

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

theorem GlobalTheory.SS.TorusSlice.goodOpen_of_equivar {G P : Over S} [GrpObj G] (i : splitTorus S X ⟶ G) (a : P ⟶ G) [IsOpenImmersion a.left]
    [IsAffine P.left] (τ : P ⟶ splitTorus S X) (hτ : Equivar i a τ)
    (hs : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (p : Z ⟶ P), ∃ p' : Z ⟶ P, p' ≫ a = (t ≫ i) * (p ≫ a)) :
    GoodOpen i (a.left ''ᵁ ⊤) := by sorry
