-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_surj
-- name    : GlobalTheory.KuennethOne.MM_surj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:17.310867+00:00
-- url     : https://prove2.me/theorems/05f12102-9d83-4ebf-b95e-46be1f20c2f2
-- title:
--   Kuenneth One: MM surj
-- statement:
--   The Kuenneth One construction uses the MM surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L113-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L113-L121

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

theorem GlobalTheory.KuennethOne.MM_surj [IsAffine S] [Finite ι] {U : ι → X.Opens} {W : Y.Opens}
    (hU : ∀ i, IsAffineOpen (U i)) (hW : IsAffineOpen W)
    (c : ∀ i, Γ(Z, p ⁻¹ᵁ U i ⊓ q ⁻¹ᵁ W)) :
    ∃ z, ∀ i, MM H U W i _ inf_le_left inf_le_right z = c i := by sorry
