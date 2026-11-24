-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_section_MM
-- name    : GlobalTheory.KuennethOne.section_MM
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:55:32.068227+00:00
-- url     : https://prove2.me/theorems/5eb05d0e-8704-43d0-a8ec-079cb6e5221b
-- title:
--   Kuenneth One: section MM
-- statement:
--   The Kuenneth One construction uses the section MM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L175-L189

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

theorem GlobalTheory.KuennethOne.section_MM {y : S ⟶ Y} (hy : y ≫ iY = 𝟙 S) {s : X ⟶ Z} (hs : s ≫ p = 𝟙 X)
    (hs' : s ≫ q = iX ≫ y) (U : ι → X.Opens) (W : Y.Opens) (e : ⊤ ≤ y ⁻¹ᵁ W) (i : ι)
    (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (hO : U i ≤ s ⁻¹ᵁ O) (z) :
    (s.appLE O (U i) hO).hom (MM H U W i O hU hW z) =
      TensorProduct.rid _ _ ((evA y hy W e).toLinearMap.lTensor _ z) i := by sorry
