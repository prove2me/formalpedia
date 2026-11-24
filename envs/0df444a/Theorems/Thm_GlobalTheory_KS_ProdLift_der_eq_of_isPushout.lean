-- Prove2me | Theorems.Thm_GlobalTheory_KS_ProdLift_der_eq_of_isPushout
-- name    : GlobalTheory.KS.ProdLift.der_eq_of_isPushout
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:00:48.771946+00:00
-- url     : https://prove2.me/theorems/bea2855e-5e23-4d8e-a67b-2e7ab2fb2403
-- title:
--   Prod Lift: der eq of is Pushout
-- statement:
--   The Prod Lift construction uses the der eq of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L73-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDerOfIsPushout.lean#L73-L92

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

theorem GlobalTheory.KS.ProdLift.der_eq_of_isPushout {R S T P : CommRingCat.{0}} {i : R ⟶ S} {j : R ⟶ T} {u : S ⟶ P}
    {v : T ⟶ P} (po : IsPushout i j u v) {B : Type} [CommRing B] (a : P →+* B) (d d' : P → B)
    (hadd : ∀ x y, d (x + y) = d x + d y)
    (hmul : ∀ x y, d (x * y) = a x * d y + a y * d x)
    (hadd' : ∀ x y, d' (x + y) = d' x + d' y)
    (hmul' : ∀ x y, d' (x * y) = a x * d' y + a y * d' x)
    (hu : ∀ x, d (u.hom x) = d' (u.hom x)) (hv : ∀ x, d (v.hom x) = d' (v.hom x)) : d = d' := by sorry
