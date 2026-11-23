-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_add_nsmul_of_torsion_characters_eq
-- name    : GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:35:56.986185+00:00
-- url     : https://prove2.me/theorems/fe94a81b-a517-4344-a998-32640a65cd46
-- title:
--   Global Theory: exists eq add nsmul of torsion characters eq
-- statement:
--   The Global Theory construction uses the exists eq add nsmul of torsion characters eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinsuppEqZeroOfSumTorsionCharactersEqZero.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FinsuppEqZeroOfSumTorsionCharactersEqZero.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinsuppEqZeroOfSumTorsionCharactersEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.exists_eq_add_nsmul_of_torsion_characters_eq (k X : Type) [Field k] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k) (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (α β : X)
    (h : ∀ t : Multiplicative X →* kˣ, t ^ N = 1 →
      t (Multiplicative.ofAdd α) = t (Multiplicative.ofAdd β)) :
    ∃ w, α = β + N • w := by sorry
