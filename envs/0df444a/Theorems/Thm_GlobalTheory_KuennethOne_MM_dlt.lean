-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_dlt
-- name    : GlobalTheory.KuennethOne.MM_dlt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:34.36684+00:00
-- url     : https://prove2.me/theorems/a9ecac98-246a-4c59-b749-c18d89fea389
-- title:
--   Kuenneth One: MM dlt
-- statement:
--   The Kuenneth One construction uses the MM dlt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L163-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L163-L173

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

theorem GlobalTheory.KuennethOne.MM_dlt (U : ι → X.Opens) (W : Y.Opens) (k : ι × ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ (U k.1 ⊓ U k.2)) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H (fun k : ι × ι => U k.1 ⊓ U k.2) W k O hU hW ((dlt iX U).rTensor _ z) =
      MM H U W k.1 O (hU.trans (p.preimage_mono inf_le_left)) hW z -
        MM H U W k.2 O (hU.trans (p.preimage_mono inf_le_right)) hW z := by sorry
