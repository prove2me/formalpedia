-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_vecOf_mid
-- name    : GlobalTheory.InertZeta.RowSpan.vecOf_mid
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:31.214934+00:00
-- url     : https://prove2.me/theorems/0d894049-dec0-4d17-8d28-a36d0070e27e
-- title:
--   Row Span: vec Of mid
-- statement:
--   The Row Span construction uses the vec Of mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L90-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L90-L91

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

theorem GlobalTheory.InertZeta.RowSpan.vecOf_mid (x₀ : L) (xm : Fin N → L) (xl : L) (k : Fin N) : vecOf x₀ xm xl (mid k) = xm k := by sorry
