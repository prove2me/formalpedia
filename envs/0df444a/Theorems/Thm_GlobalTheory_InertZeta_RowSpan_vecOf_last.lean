-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_last
-- name    : GlobalTheory.InertZeta.RowSpan.vecOf_last
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:49:42.247507+00:00
-- url     : https://prove2.me/theorems/2f14d00e-46cb-49fb-8e06-e2379e8a6401
-- title:
--   Row Span: vec Of last
-- statement:
--   The Row Span construction uses the vec Of last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L92-L93

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

theorem GlobalTheory.InertZeta.RowSpan.vecOf_last (x₀ : L) (xm : Fin N → L) (xl : L) : vecOf x₀ xm xl (Fin.last (N + 1)) = xl := by sorry
