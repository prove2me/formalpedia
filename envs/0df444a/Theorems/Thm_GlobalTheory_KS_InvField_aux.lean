-- Prove2me | Theorems.Thm_GlobalTheory_KS_InvField_aux
-- name    : GlobalTheory.KS.InvField.aux
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:16.802387+00:00
-- url     : https://prove2.me/theorems/e6c2910f-a494-476c-a8c1-78da7e954838
-- title:
--   Inv Field: aux
-- statement:
--   The Inv Field construction uses the aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueInvariantVectorFieldOfTangent.lean#L50-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueInvariantVectorFieldOfTangent.lean#L50-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructureStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvField

theorem GlobalTheory.KS.InvField.aux {K : Type} [Field K] {Y Y' : Scheme.{0}} (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ T : Y' ⟶ Y)
    (j : Y ⟶ Y') (hp : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (hρ : j ≫ ρ = 𝟙 Y)
    (hπ : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) (hT : j ≫ T = 𝟙 Y) (hq : T ≫ q = ρ ≫ q)
    (P : (∀ W : Y.Opens, Γ(Y, W) → Γ(Y, W)) → Prop)
    (hP : ∀ dd, P dd ↔ ∀ (W : Y.Opens) (f : Γ(Y, W)), pbT T f (ρ ⁻¹ᵁ W) =
      pbT ρ f (ρ ⁻¹ᵁ W) + constFn π _ DualNumber.eps * pbT ρ (dd W f) (ρ ⁻¹ᵁ W)) :
    (∃ dd, P dd) ∧ ∀ dd, P dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(Y, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn q W a) = 0) ∧ ∀ dd', P dd' → dd' = dd := by sorry
