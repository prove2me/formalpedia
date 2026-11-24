-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_RowSpan_rho_mul
-- name    : GlobalTheory.InertZeta.RowSpan.rho_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:10.184012+00:00
-- url     : https://prove2.me/theorems/87b0121d-d3af-4d1b-93d1-8d05e30e25c3
-- title:
--   Row Span: rho mul
-- statement:
--   The Row Span construction uses the rho mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L155-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean#L155-L183

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

theorem GlobalTheory.InertZeta.RowSpan.rho_mul {a : ℤ} {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b r : Fin N → L}
    {c y z : L} (hg10 : ∀ i, g (mid i) 0 = 0) (hg11 : ∀ i j, g (mid i) (mid j) = g₀ i j)
    (hg12 : ∀ i, g (mid i) (Fin.last (N + 1)) = (g₀ *ᵥ b) i) (hCM : C * (U + V * g₀) = 1) (hy : y ≠ 0) :
    vecOf 0 (fun j => z * (r ᵥ* C) j) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ* rowsP a g U V y =
      vecOf 0 (fun j => z * r j) (z * c) := by sorry
