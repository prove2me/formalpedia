-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_eq
-- name    : GlobalTheory.KuennethOne.MM_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:35.795531+00:00
-- url     : https://prove2.me/theorems/0e01b589-c1bf-4c0b-8122-44c9cb17d7be
-- title:
--   Kuenneth One: MM eq
-- statement:
--   The Kuenneth One construction uses the MM eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L105-L111

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

theorem GlobalTheory.KuennethOne.MM_eq [Fintype ι] [DecidableEq ι] (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens)
    (hU : O ≤ p ⁻¹ᵁ U i) (hW : O ≤ q ⁻¹ᵁ W) (z) :
    MM H U W i O hU hW z = mm H (U i) W O hU hW (TensorProduct.piLeft _ _ _ z i) := by sorry
