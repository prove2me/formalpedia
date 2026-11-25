-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroSmulMemSpanLattice_exists_ne_zero_smul_mem
-- name    : GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:15.925775+00:00
-- url     : https://prove2.me/theorems/1528e06a-7821-46b0-8db2-30ff9e83b6f0
-- title:
--   Nonzero Smul Mem Span Lattice: exists ne zero smul mem
-- statement:
--   The Nonzero Smul Mem Span Lattice construction uses the exists ne zero smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisBis.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisBis.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.NonzeroSmulMemSpanLattice

theorem GlobalTheory.NonzeroSmulMemSpanLattice.exists_ne_zero_smul_mem {E : Type u_1} {V : Type u_2} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (Λ : Submodule (NumberField.RingOfIntegers E) V) (hΛ : Submodule.IsLattice E Λ) (v : V) :
    ∃ o : NumberField.RingOfIntegers E, o ≠ 0 ∧ o • v ∈ Λ := by sorry
