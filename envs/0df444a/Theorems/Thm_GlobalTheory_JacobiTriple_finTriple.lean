-- Prove2me | Theorems.Thm_GlobalTheory_JacobiTriple_finTriple
-- name    : GlobalTheory.JacobiTriple.finTriple
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:40:04.195619+00:00
-- url     : https://prove2.me/theorems/19207592-d19b-553d-9139-e9f7bbf0ae17
-- title:
--   Jacobi Triple: fin Triple
-- statement:
--   The Jacobi Triple construction uses the fin Triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProduct.lean#L35-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProduct.lean#L35-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple

theorem GlobalTheory.JacobiTriple.finTriple (s x : ℂ) (hs : s ≠ 0) (hs1 : ‖s‖ < 1) (hx : x ≠ 0) (n : ℕ) :
    ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) =
      ∑ j ∈ Finset.Icc (-(n : ℤ)) n, finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by sorry
