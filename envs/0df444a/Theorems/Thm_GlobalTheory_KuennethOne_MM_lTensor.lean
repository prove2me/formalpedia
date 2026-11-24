-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_lTensor
-- name    : GlobalTheory.KuennethOne.MM_lTensor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:32.234499+00:00
-- url     : https://prove2.me/theorems/71cd580d-8ae7-43bd-a0bc-b1bb7865f3ff
-- title:
--   Kuenneth One: MM l Tensor
-- statement:
--   The Kuenneth One construction uses the MM l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L144-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L144-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitsOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TensorProduct
open GlobalTheory GlobalTheory.KuennethOne
variable {S X Y Z T : Scheme.{0}}
variable {p : Z ⟶ X} {q : Z ⟶ Y} {iX : X ⟶ S} {iY : Y ⟶ S} (H : IsPullback p q iX iY)
variable {ι : Type}

theorem GlobalTheory.KuennethOne.MM_lTensor (U : ι → X.Opens) {W W' : Y.Opens} (h : W' ≤ W) (i : ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W') (z) :
    MM H U W' i O hU hW ((rsA iY h).toLinearMap.lTensor _ z) =
      MM H U W i O hU (hW.trans (q.preimage_mono h)) z := by sorry
