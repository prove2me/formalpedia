-- Prove2me | Theorems.Thm_GlobalTheory_nsmul_surjective_torsion_lift
-- name    : GlobalTheory.nsmul_surjective_torsion_lift
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:53.486315+00:00
-- url     : https://prove2.me/theorems/b3157b11-3fef-4ed7-80d7-2930cc8b5ef8
-- title:
--   Global Theory: nsmul surjective torsion lift
-- statement:
--   The Global Theory construction uses the nsmul surjective torsion lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionLiftNumberFieldModule.lean#L6-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionLiftNumberFieldModule.lean#L6-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionLiftNumberFieldModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.nsmul_surjective_torsion_lift (M : Type) [AddCommGroup M] (N e : ℕ) (hN : 1 ≤ N)
    (h : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ e)
    (j : ℕ) (y : M) (hy : (N ^ j) • y = 0) :
    ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by sorry
