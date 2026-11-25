-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Kron_exists_annihilator
-- name    : GlobalTheory.Nef.Kron.exists_annihilator
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:01.579523+00:00
-- url     : https://prove2.me/theorems/006603c1-3e82-4b1f-b633-b975c9c06e73
-- title:
--   Kron: exists annihilator
-- statement:
--   The Kron construction uses the exists annihilator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L66-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L66-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)

theorem GlobalTheory.Nef.Kron.exists_annihilator (N : ℕ) (hN : ∀ n, N ≤ n → hankel c n = 0) :
    ∃ q : F[X], q ≠ 0 ∧ ∀ j, ev c (q * X ^ j) = 0 := by sorry
