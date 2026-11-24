-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rowM_mid
-- name    : GlobalTheory.InertZeta.RowSpan.rowM_mid
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:34.804201+00:00
-- url     : https://prove2.me/theorems/ad8947e4-664e-4fe7-a36a-b9f89e582ae3
-- title:
--   Row Span: row M mid
-- statement:
--   The Row Span construction uses the row M mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L19-L21

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
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {b : Fin N → L}

theorem GlobalTheory.InertZeta.RowSpan.rowM_mid (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j) (k j : Fin N) :
    rowM g U V k (mid j) = (U + V * g₀) k j := by sorry
