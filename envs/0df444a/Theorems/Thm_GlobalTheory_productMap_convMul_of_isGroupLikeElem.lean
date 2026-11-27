-- Prove2me | Theorems.Thm_GlobalTheory_productMap_convMul_of_isGroupLikeElem
-- name    : GlobalTheory.productMap_convMul_of_isGroupLikeElem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:04.659776+00:00
-- url     : https://prove2.me/theorems/1e84dbc2-7af2-44a1-be45-f47593728cb3
-- title:
--   Global Theory: product Map conv Mul of is Group Like Elem
-- statement:
--   The Global Theory construction uses the product Map conv Mul of is Group Like Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1193-L1199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1193-L1199

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
variable [CommSemiring K] [Bialgebra R K] {x : A ⊗[R] K} {B : Type*} [CommSemiring B] [Algebra R B]

theorem GlobalTheory.productMap_convMul_of_isGroupLikeElem (hx : IsGroupLikeElem A x) (g : A →ₐ[R] B)
    (y y' : WithConv (K →ₐ[R] B)) :
    productMap g (y * y').ofConv x = productMap g y.ofConv x * productMap g y'.ofConv x := by sorry
