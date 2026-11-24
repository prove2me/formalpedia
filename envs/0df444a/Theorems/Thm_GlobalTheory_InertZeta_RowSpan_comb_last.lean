-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_comb_last
-- name    : GlobalTheory.InertZeta.RowSpan.comb_last
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:49:50.117828+00:00
-- url     : https://prove2.me/theorems/1ff8abbe-8e18-47df-861c-745a79e0a2f8
-- title:
--   Row Span: comb last
-- statement:
--   The Row Span construction uses the comb last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L35-L37

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

theorem GlobalTheory.InertZeta.RowSpan.comb_last (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (A : Matrix (Fin N) (Fin N) L) (i : Fin N) :
    (∑ k, A i k • rowM g U V k) (Fin.last (N + 1)) = (A *ᵥ (V *ᵥ (g₀ *ᵥ b))) i := by sorry
