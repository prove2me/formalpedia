-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_exists_basis
-- name    : GlobalTheory.QuadraticZeta.exists_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T17:33:34.94672+00:00
-- url     : https://prove2.me/theorems/bf26e243-18b8-492e-9e6f-c9cbef4a73d6
-- title:
--   Quadratic Zeta: exists basis
-- statement:
--   The Quadratic Zeta construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L66-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L66-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K]

theorem GlobalTheory.QuadraticZeta.exists_basis (h2 : finrank ℚ K = 2) :
    ∃ (b : Basis (Fin 2) ℤ (𝓞 K)) (t n : ℤ), b 0 = 1 ∧ b 1 ^ 2 = t * b 1 - n ∧
      discr K = t ^ 2 - 4 * n := by sorry
