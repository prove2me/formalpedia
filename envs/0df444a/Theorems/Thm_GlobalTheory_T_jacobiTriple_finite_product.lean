-- Prove2me | Theorems.Thm_GlobalTheory_T_jacobiTriple_finite_product
-- name    : GlobalTheory.T.jacobiTriple_finite_product
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:41:58.467863+00:00
-- url     : https://prove2.me/theorems/297cc0ea-dd38-4857-855c-65f607426280
-- title:
--   T: jacobi Triple finite product
-- statement:
--   The T construction uses the jacobi Triple finite product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProductStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteProductStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProduct
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteProductStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.jacobiTriple_finite_product : ∀ (s x : ℂ), s ≠ 0 → ‖s‖ < 1 → x ≠ 0 → ∀ n : ℕ, ∏ k ∈ Finset.range n, ((1 + x * s ^ (2 * k + 1)) * (1 + x⁻¹ * s ^ (2 * k + 1))) = ∑ j ∈ Finset.Icc (-(n : ℤ)) n, GlobalTheory.JacobiTriple.finCoeff (s ^ 2) n j * (x ^ j * s ^ (j ^ 2)) := by sorry
