-- Prove2me | Theorems.Thm_GlobalTheory_KS_ProdLift_exists_der_of_isPushout
-- name    : GlobalTheory.KS.ProdLift.exists_der_of_isPushout
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:48.441987+00:00
-- url     : https://prove2.me/theorems/c106a605-ac21-4e2a-8602-9c87d759d2a0
-- title:
--   Prod Lift: exists der of is Pushout
-- statement:
--   The Prod Lift construction uses the exists der of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L32-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L32-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift

theorem GlobalTheory.KS.ProdLift.exists_der_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (δ : S → B) (δ' : T → B)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hmul : ∀ x y, δ (x * y) = a (u.hom x) * δ y + a (u.hom y) * δ x)
    (hadd' : ∀ x y, δ' (x + y) = δ' x + δ' y)
    (hmul' : ∀ x y, δ' (x * y) = a (v.hom x) * δ' y + a (v.hom y) * δ' x)
    (hR : ∀ r, δ (i.hom r) = δ' (j.hom r)) :
    ∃ d : P → B, (∀ x y, d (x + y) = d x + d y) ∧ (∀ x y, d (x * y) = a x * d y + a y * d x) ∧
      (∀ x, d (u.hom x) = δ x) ∧ ∀ x, d (v.hom x) = δ' x := by sorry
