-- Prove2me | Theorems.Thm_GlobalTheory_TripleMap_exists_rigidified
-- name    : GlobalTheory.TripleMap.exists_rigidified
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:20.414794+00:00
-- url     : https://prove2.me/theorems/d785cf37-b82e-5017-92b8-be1397eaa59b
-- title:
--   Triple Map: exists rigidified
-- statement:
--   The Triple Map construction uses the exists rigidified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSabMapOfLbIso.lean#L38-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothGeometricallyIntegralAbLocusTensorObj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.TripleMap

theorem GlobalTheory.TripleMap.exists_rigidified {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) (e : S ⟶ X) (e' : S' ⟶ X') (p : X' ⟶ S')
    (hp : e' ≫ p = 𝟙 _) (f : S' ⟶ S) (he : e' ≫ F = f ≫ e) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) ρ' ρ f := by sorry
