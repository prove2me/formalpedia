-- Prove2me | Theorems.Thm_GlobalTheory_KuennethOne_MM_tmul
-- name    : GlobalTheory.KuennethOne.MM_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:43.104316+00:00
-- url     : https://prove2.me/theorems/fe7426af-2ac2-49b1-806c-4385ddd1c60a
-- title:
--   Kuenneth One: MM tmul
-- statement:
--   The Kuenneth One construction uses the MM tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/MemRangeRTensorOfForallDual.lean#L101-L103

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

theorem GlobalTheory.KuennethOne.MM_tmul (U : ι → X.Opens) (W : Y.Opens) (i : ι) (O : Z.Opens) (hU : O ≤ p ⁻¹ᵁ U i)
    (hW : O ≤ q ⁻¹ᵁ W) (a : ∀ i, Fn iX (U i)) (b : Fn iY W) :
    MM H U W i O hU hW (a ⊗ₜ b) = (p.appLE (U i) O hU).hom (a i) * (q.appLE W O hW).hom b := by sorry
