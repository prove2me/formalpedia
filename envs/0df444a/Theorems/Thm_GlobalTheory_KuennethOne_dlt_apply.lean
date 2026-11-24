-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_dlt_apply
-- name    : GlobalTheory.KuennethOne.dlt_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:27.208562+00:00
-- url     : https://prove2.me/theorems/b4b8f807-2ff6-4d72-ba3c-f7644b0bf2e9
-- title:
--   Kuenneth One: dlt apply
-- statement:
--   The Kuenneth One construction uses the dlt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L160-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L160-L161

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

theorem GlobalTheory.KuennethOne.dlt_apply (iX : X ⟶ S) (U : ι → X.Opens) (x : ∀ i, Fn iX (U i)) (k : ι × ι) :
    dlt iX U x k = (rs inf_le_left (x k.1) - rs inf_le_right (x k.2) : Γ(X, U k.1 ⊓ U k.2)) := by sorry
