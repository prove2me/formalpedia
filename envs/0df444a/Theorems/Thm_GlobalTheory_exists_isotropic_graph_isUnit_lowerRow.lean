-- Prove2me | Theorems.Thm_GlobalTheory_exists_isotropic_graph_isUnit_lowerRow
-- name    : GlobalTheory.exists_isotropic_graph_isUnit_lowerRow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:34:15.393872+00:00
-- url     : https://prove2.me/theorems/bc6e01f8-c79c-43b4-b788-327bfcfe9c12
-- title:
--   Global Theory: exists isotropic graph is Unit lower Row
-- statement:
--   The Global Theory construction uses the exists isotropic graph is Unit lower Row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphUnitaryIsUnitLowerBlock.lean#L8-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsotropicGraphUnitaryIsUnitLowerBlock.lean#L8-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftModMaximalSkewStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphDetLowerRowNeZeroFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsotropicGraphUnitaryIsUnitLowerBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory

theorem GlobalTheory.exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by sorry
