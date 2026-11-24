-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_inj
-- name    : GlobalTheory.KuennethOne.MM_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:33.333745+00:00
-- url     : https://prove2.me/theorems/1c73fab8-1b65-4b21-84be-445e6b125b07
-- title:
--   Kuenneth One: MM inj
-- statement:
--   The Kuenneth One construction uses the MM inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L123-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L123-L132

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

theorem GlobalTheory.KuennethOne.MM_inj [IsAffine S] [Finite ι] {U : ι → X.Opens} {W : Y.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W) (z)
    (h : ∀ i, MM H U W i _ inf_le_left inf_le_right z = 0) : z = 0 := by sorry
