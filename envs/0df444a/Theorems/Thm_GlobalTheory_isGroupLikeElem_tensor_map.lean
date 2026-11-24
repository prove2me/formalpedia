-- Prove2me | Theorems.Thm_GlobalTheory_isGroupLikeElem_tensor_map
-- name    : GlobalTheory.isGroupLikeElem_tensor_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:55.964348+00:00
-- url     : https://prove2.me/theorems/d1309da2-d538-4d88-b99b-ba00ed7b8344
-- title:
--   Global Theory: is Group Like Elem tensor map
-- statement:
--   The Global Theory construction uses the is Group Like Elem tensor map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1408-L1437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1408-L1437

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
open CartierDual
variable {R : Type*} [CommSemiring R]

theorem GlobalTheory.isGroupLikeElem_tensor_map {A B K K' : Type*} [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra R B] [Semiring K] [Bialgebra R K] [Semiring K'] [Bialgebra R K']
    {x : A ⊗[R] K} (hx : IsGroupLikeElem A x) (g : A →ₐ[R] B) (f : K →ₐc[R] K') :
    IsGroupLikeElem B (Algebra.TensorProduct.map g (f : K →ₐ[R] K') x) := by sorry
