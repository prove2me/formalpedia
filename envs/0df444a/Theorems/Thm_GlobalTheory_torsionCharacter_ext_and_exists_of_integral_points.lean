-- Prove2me | Theorems.Thm_GlobalTheory_torsionCharacter_ext_and_exists_of_integral_points
-- name    : GlobalTheory.torsionCharacter_ext_and_exists_of_integral_points
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:57.700525+00:00
-- url     : https://prove2.me/theorems/588524ba-a457-4956-ba92-ea28b5aa6e59
-- title:
--   Global Theory: torsion Character ext and exists of integral points
-- statement:
--   The Global Theory construction uses the torsion Character ext and exists of integral points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCharacterExtAndExistsOfIntegralPoints.lean#L62-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCharacterExtAndExistsOfIntegralPoints.lean#L62-L171

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
open GlobalTheory
open KernelNoTorsion TangentPow TorsionCharacter GmPoints

theorem GlobalTheory.torsionCharacter_ext_and_exists_of_integral_points :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G], ∀ N : ℕ, 1 ≤ N → IsFinite (torsion G N).hom → Flat (torsion G N).hom → (∀ f f' : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), (∀ w : specO O O ⟶ torsion G N, w ≫ f = w ≫ f') → f = f') ∧ ∀ κ : (specO O O ⟶ G) → Cˣ, (∀ x y : specO O O ⟶ G, x ^ N = 1 → y ^ N = 1 → κ (x * y) = κ x * κ y) → ∃ f : torsion G N ⟶ Gm (Spec (CommRingCat.of O)), IsCharTors G N f ∧ ∀ w : specO O O ⟶ torsion G N, algebraMap O C (unitOf (w ≫ f) : O) = (κ (w ≫ torsion.ι G N) : C) := by sorry
