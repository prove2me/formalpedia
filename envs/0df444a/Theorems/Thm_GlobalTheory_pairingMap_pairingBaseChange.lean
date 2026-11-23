-- Prove2me | Theorems.Thm_GlobalTheory_pairingMap_pairingBaseChange
-- name    : GlobalTheory.pairingMap_pairingBaseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:21:21.50035+00:00
-- url     : https://prove2.me/theorems/6fbb2664-5f35-4b69-907a-520ab63634b2
-- title:
--   Global Theory: pairing Map pairing Base Change
-- statement:
--   The Global Theory construction uses the pairing Map pairing Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1462-L1475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/MemPrimitiveTensorsIffIsPrimitiveElem.lean#L1462-L1475

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
variable {H K : Type*} [CommSemiring H] [Bialgebra R H] [CommSemiring K] [Bialgebra R K]
  {u : H ⊗[R] K}
variable (A : Type*) [CommSemiring A] [Algebra R A]

theorem GlobalTheory.pairingMap_pairingBaseChange (u : H ⊗[R] K) (x : A ⊗[R] CartierDual R H) :
    pairingMap A (pairingBaseChange A u) (baseChangeLinear R A H x) =
      (pairingMap R u).baseChange A x := by sorry
