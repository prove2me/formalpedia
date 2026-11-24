-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowsP_last
-- name    : GlobalTheory.InertZeta.RowSpan.rowsP_last
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:49:36.833407+00:00
-- url     : https://prove2.me/theorems/843b0d55-7847-48ee-a074-262cff8a2d0a
-- title:
--   Row Span: rows P last
-- statement:
--   The Row Span construction uses the rows P last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L56-L58

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

theorem GlobalTheory.InertZeta.RowSpan.rowsP_last :
    rowsP a g U V y (Fin.last (N + 1)) = y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by sorry
