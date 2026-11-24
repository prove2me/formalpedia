-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_zero_ne_mid
-- name    : GlobalTheory.InertZeta.RowSpan.zero_ne_mid
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:26.118807+00:00
-- url     : https://prove2.me/theorems/218fedd5-c2ae-4a23-83c6-1d172df68892
-- title:
--   Row Span: zero ne mid
-- statement:
--   The Row Span construction uses the zero ne mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L125-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L125-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.InertZeta.RowSpan.zero_ne_mid (j : Fin N) : (0 : Fin (N + 2)) ≠ mid j := by sorry
