-- Prove2me | Theorems.Thm_GlobalTheory_isGroupLikeElem_tensor_iff
-- name    : GlobalTheory.isGroupLikeElem_tensor_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:20:11.413799+00:00
-- url     : https://prove2.me/theorems/27e1151a-db48-4196-9958-2f16c2ab33fd
-- title:
--   Global Theory: is Group Like Elem tensor iff
-- statement:
--   The Global Theory construction uses the is Group Like Elem tensor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1156-L1181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1156-L1181

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra HopfAlgebra WithConv
open GlobalTheory
open Algebra.TensorProduct (includeLeft includeRight productMap)
variable {R A K : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem GlobalTheory.isGroupLikeElem_tensor_iff [Semiring K] [Bialgebra R K] (x : A ⊗[R] K) :
    IsGroupLikeElem A x ↔ TensorProduct.rid R A (LinearMap.lTensor A counit x) = 1 ∧
      LinearMap.lTensor A comul x =
        Algebra.TensorProduct.map (AlgHom.id R A) (includeLeft : K →ₐ[R] K ⊗[R] K) x *
          Algebra.TensorProduct.map (AlgHom.id R A) (includeRight : K →ₐ[R] K ⊗[R] K) x := by sorry
