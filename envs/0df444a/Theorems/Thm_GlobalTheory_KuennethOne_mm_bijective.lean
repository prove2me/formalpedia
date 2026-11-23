-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_mm_bijective
-- name    : GlobalTheory.KuennethOne.mm_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:44.059634+00:00
-- url     : https://prove2.me/theorems/1d14ce94-e266-4f41-be5f-0eb6c98184ab
-- title:
--   Kuenneth One: mm bijective
-- statement:
--   The Kuenneth One construction uses the mm bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L73-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L73-L93

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

theorem GlobalTheory.KuennethOne.mm_bijective [IsAffine S] {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U)
    (hW : IsAffineOpen W) :
    Function.Bijective (mm H U W (p ⁻¹ᵁ U ⊓ q ⁻¹ᵁ W) inf_le_left inf_le_right) := by sorry
