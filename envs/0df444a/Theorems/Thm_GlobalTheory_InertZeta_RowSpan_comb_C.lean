-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_C
-- name    : GlobalTheory.InertZeta.RowSpan.comb_C
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:18:58.468546+00:00
-- url     : https://prove2.me/theorems/c9bba3c8-7283-4114-a2ca-0e8265f67ca7
-- title:
--   Row Span: comb C
-- statement:
--   The Row Span construction uses the comb C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L132-L139

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
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}

theorem GlobalTheory.InertZeta.RowSpan.comb_C (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (i : Fin N) :
    ∑ k, C i k • rowM g U V k = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) +
      ((C * V * g₀) *ᵥ b) i • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) := by sorry
