-- Prove2me | Theorems.Thm_GlobalTheory_LieEtale_existsUnique_tangent_lift
-- name    : GlobalTheory.LieEtale.existsUnique_tangent_lift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:03:12.190804+00:00
-- url     : https://prove2.me/theorems/de1a5a8c-8cc8-4662-869b-b1fb556eb1ad
-- title:
--   Lie Etale: exists Unique tangent lift
-- statement:
--   The Lie Etale construction uses the exists Unique tangent lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L161-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTangentLift.lean#L161-L170

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTangentLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LieEtale
variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem GlobalTheory.LieEtale.existsUnique_tangent_lift {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by sorry
