-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_zero_ne_last
-- name    : GlobalTheory.InertZeta.RowSpan.zero_ne_last
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:06.856439+00:00
-- url     : https://prove2.me/theorems/b25e4a34-8655-4da2-81eb-5ffacdb98037
-- title:
--   Row Span: zero ne last
-- statement:
--   The Row Span construction uses the zero ne last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L123-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L123-L123

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

theorem GlobalTheory.InertZeta.RowSpan.zero_ne_last : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := by sorry
