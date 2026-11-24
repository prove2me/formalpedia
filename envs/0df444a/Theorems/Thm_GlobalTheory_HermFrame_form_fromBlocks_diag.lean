-- Prove2me | Theorems.Thm_GlobalTheory_HermFrame_form_fromBlocks_diag
-- name    : GlobalTheory.HermFrame.form_fromBlocks_diag
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:38.335802+00:00
-- url     : https://prove2.me/theorems/3fa45f09-c19a-415e-82d8-e959b4a3a239
-- title:
--   Herm Frame: form from Blocks diag
-- statement:
--   The Herm Frame construction uses the form from Blocks diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {m l m' l' : Type*}
variable [Fintype m] [Fintype l] [Fintype m'] [Fintype l']

theorem GlobalTheory.HermFrame.form_fromBlocks_diag (A₁ : Matrix m m ℂ) (A₂ : Matrix l l ℂ) (u u' : m → ℂ)
    (w w' : l → ℂ) : form (fromBlocks A₁ 0 0 A₂) (Sum.elim u w) (Sum.elim u' w') =
      form A₁ u u' + form A₂ w w' := by sorry
