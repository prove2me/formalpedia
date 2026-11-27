-- Prove2me | Theorems.Thm_GlobalTheory_JacobiTriple_finTriple_sum_odd
-- name    : GlobalTheory.JacobiTriple.finTriple_sum_odd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:41:13.628375+00:00
-- url     : https://prove2.me/theorems/ece74547-6348-4f68-a71e-41f1b3fe85a2
-- title:
--   Jacobi Triple: fin Triple sum odd
-- statement:
--   The Jacobi Triple construction uses the fin Triple sum odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProduct.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProduct.lean#L9-L12

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

theorem GlobalTheory.JacobiTriple.finTriple_sum_odd (n : ℕ) : ∑ k ∈ Finset.range n, (2 * k + 1) = n ^ 2 := by sorry
