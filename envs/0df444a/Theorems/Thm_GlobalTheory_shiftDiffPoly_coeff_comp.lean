-- Prove2me | Theorems.Thm_GlobalTheory_shiftDiffPoly_coeff_comp
-- name    : GlobalTheory.shiftDiffPoly_coeff_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:10.931873+00:00
-- url     : https://prove2.me/theorems/a22a59d8-b761-475d-8f73-93232ec88c0e
-- title:
--   Global Theory: shift Diff Poly coeff comp
-- statement:
--   The Global Theory construction uses the shift Diff Poly coeff comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L6-L9

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

theorem GlobalTheory.shiftDiffPoly_coeff_comp (f : ℂ[X]) (n : ℕ) :
    (f.comp (X + 1)).coeff n = ∑ i ∈ range (f.natDegree + 1), f.coeff i * (i.choose n : ℂ) := by sorry
