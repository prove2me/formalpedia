-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_mid
-- name    : GlobalTheory.InertZeta.RowSpan.rowsP_mid
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:51:08.763483+00:00
-- url     : https://prove2.me/theorems/2194bfe0-c267-48d4-a0bf-de62b3e9074a
-- title:
--   Row Span: rows P mid
-- statement:
--   The Row Span construction uses the rows P mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L53-L54

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
variable (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L)

theorem GlobalTheory.InertZeta.RowSpan.rowsP_mid (k : Fin N) : rowsP a g U V y (mid k) = rowM g U V k := by sorry
