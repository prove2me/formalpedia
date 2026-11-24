-- Prove2me | Theorems.Thm_GlobalTheory_GenericHom_hom_ext_points
-- name    : GlobalTheory.GenericHom.hom_ext_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:08.539831+00:00
-- url     : https://prove2.me/theorems/5367b448-8339-4665-b037-c7d8253a7ed1
-- title:
--   Generic Hom: hom ext points
-- statement:
--   The Generic Hom construction uses the hom ext points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMonHomExtension.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMonHomExtension.lean#L64-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsMonHomExtension
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
open GlobalTheory GlobalTheory.GenericHom
variable {k : Type} [Field k] [IsAlgClosed k]

theorem GlobalTheory.GenericHom.hom_ext_points {X Y : Over (Sp k)}
    [Smooth X.hom] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by sorry
