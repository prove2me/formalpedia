-- Prove2me | Theorems.Thm_GlobalTheory_TorsionCharacterExt_tensor_eq_zero_of_forall_pair
-- name    : GlobalTheory.TorsionCharacterExt.tensor_eq_zero_of_forall_pair
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:11.457684+00:00
-- url     : https://prove2.me/theorems/86b30317-af7b-4e69-96ba-d916856b66de
-- title:
--   Torsion Character Ext: tensor eq zero of forall pair
-- statement:
--   The Torsion Character Ext construction uses the tensor eq zero of forall pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCharacterExtAndExistsOfIntegralPoints.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCharacterExtAndExistsOfIntegralPoints.lean#L19-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsAlgHomValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SectionEqZeroOfForallGeometricPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEvalEqOfMultiplicativeOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCharacterExtAndExistsOfIntegralPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCharacterExt
open Algebra.TensorProduct

theorem GlobalTheory.TorsionCharacterExt.tensor_eq_zero_of_forall_pair (O F : Type) [CommRing O] [Field F] [IsAlgClosed F]
    [Algebra O F] [Module.Flat O F] (hinj : Function.Injective (algebraMap O F)) (A : Type)
    [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A]
    [_root_.IsReduced (F ⊗[O] A)] (t : A ⊗[O] A)
    (ht : ∀ x y : A →ₐ[O] F, lift x y (fun _ _ => Commute.all _ _) t = 0)
    (hmul : Function.Injective (LinearMap.mul' O F)) : t = 0 := by sorry
