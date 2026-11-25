-- Prove2me | Theorems.Thm_GlobalTheory_GenericHom_exists_monHom_extension
-- name    : GlobalTheory.GenericHom.exists_monHom_extension
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:13:28.242337+00:00
-- url     : https://prove2.me/theorems/77acb531-b483-57f9-9ecb-751a4e576e0b
-- title:
--   Generic Hom: exists mon Hom extension
-- statement:
--   The Generic Hom construction uses the exists mon Hom extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMonHomExtension.lean#L121-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsMonHomExtension.lean#L121-L214

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

theorem GlobalTheory.GenericHom.exists_monHom_extension : ∀ (k : Type) [Field k] [IsAlgClosed k] (H G U : Over (Sp k)) [GrpObj H] [GrpObj G], SmConn H → SmConn G → ∀ (j : U ⟶ H) (f : U ⟶ G), IsOpenImmersion j.left → Nonempty U.left → (∀ x y z : (𝟙_ (Over (Sp k)) ⟶ U), (x ≫ j) * (y ≫ j) = z ≫ j → (x ≫ f) * (y ≫ f) = z ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by sorry
