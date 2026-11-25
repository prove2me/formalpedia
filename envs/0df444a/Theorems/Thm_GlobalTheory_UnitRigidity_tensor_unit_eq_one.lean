-- Prove2me | Theorems.Thm_GlobalTheory_UnitRigidity_tensor_unit_eq_one
-- name    : GlobalTheory.UnitRigidity.tensor_unit_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:19:33.199849+00:00
-- url     : https://prove2.me/theorems/348a354b-e5b3-46cb-bd2c-c8dca01561f1
-- title:
--   Unit Rigidity: tensor unit eq one
-- statement:
--   The Unit Rigidity construction uses the tensor unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L140-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GeometricallyConnectedOfIsPullbackOfSurjective.lean#L140-L187

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnitOnProductEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GeometricallyConnectedOfIsPullbackOfSurjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.UnitRigidity

theorem GlobalTheory.UnitRigidity.tensor_unit_eq_one {K A B : Type} [Field K] [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A]
    [CommRing B] [Algebra K B]
    (hB : ∀ (F : Type) [Field F] [Algebra K F], NoZeroDivisors (F ⊗[K] B))
    (φ : A →ₐ[K] K) (ψ : B →ₐ[K] K) (u : A ⊗[K] B) (hu : IsUnit u)
    (h1 : Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp ψ)
      (fun _ _ => Commute.all _ _) u = 1)
    (h2 : Algebra.TensorProduct.lift ((Algebra.ofId K B).comp φ) (AlgHom.id K B)
      (fun _ _ => Commute.all _ _) u = 1) : u = 1 := by sorry
