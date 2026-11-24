-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_unipotent_size_reduction_column
-- name    : GlobalTheory.ClassFin.unipotent_size_reduction_column
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:50.548553+00:00
-- url     : https://prove2.me/theorems/661e970b-0404-40f9-bdc9-ee4fb8a8844a
-- title:
--   Class Fin: unipotent size reduction column
-- statement:
--   The Class Fin construction uses the unipotent size reduction column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnipotentUpperSizeReduction.lean#L8-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnipotentUpperSizeReduction.lean#L8-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnipotentUpperSizeReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.unipotent_size_reduction_column {N : ℕ} (n : Matrix (Fin N) (Fin N) ℝ)
    (h1 : ∀ i, n i i = 1) (h0 : ∀ i j, j < i → n i j = 0) (j : Fin N) (k : ℕ) :
    ∃ z : Fin N → ℤ, z j = 1 ∧ (∀ l, j < l → z l = 0) ∧
      ∀ i, i < j → (j : ℕ) ≤ i + k → |∑ l, n i l * (z l : ℝ)| ≤ 1 / 2 := by sorry
