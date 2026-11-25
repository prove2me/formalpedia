-- Prove2me | Theorems.Thm_GlobalTheory_SS_TorusSlice_exists_goodOpen
-- name    : GlobalTheory.SS.TorusSlice.exists_goodOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:57.024796+00:00
-- url     : https://prove2.me/theorems/94a94495-36bf-4575-b1ef-4ba970b0bcc4
-- title:
--   Torus Slice: exists good Open
-- statement:
--   The Torus Slice construction uses the exists good Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L212-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorusStableGoodOpenOfWeightUnits.lean#L212-L255

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

theorem GlobalTheory.SS.TorusSlice.exists_goodOpen [IsAffine S] [Module.Finite ℤ X] {G Y : Over S} [GrpObj G] [QuasiSeparated G.hom]
    (i : splitTorus S X ⟶ G) [IsMonHom i] (j : Y ⟶ G) [IsOpenImmersion j.left] [IsAffine Y.left]
    (σ₀ : Y ⟶ splitTorus S X) (h₀ : Equivar i j σ₀) (y : 𝟙_ (Over S) ⟶ Y) :
    ∃ V, GoodOpen i V ∧ ∀ s, (y ≫ j).left s ∈ V := by sorry
