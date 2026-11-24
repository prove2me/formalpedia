-- Prove2me | Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_sub
-- name    : GlobalTheory.shiftDiffPoly_coeff_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:12.557774+00:00
-- url     : https://prove2.me/theorems/b8d7b88f-8371-41f8-b036-2a2a87607b98
-- title:
--   Global Theory: shift Diff Poly coeff sub
-- statement:
--   The Global Theory construction uses the shift Diff Poly coeff sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open GlobalTheory

theorem GlobalTheory.shiftDiffPoly_coeff_sub (f : ℂ[X]) (e : ℕ) (he : f.natDegree = e + 1) :
    (f.comp (X + 1) - f).coeff e = ((e : ℂ) + 1) * f.coeff (e + 1) := by sorry
