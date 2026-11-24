-- Prove2me | Theorems.Thm_GlobalTheory_FrameDet_exists_lower
-- name    : GlobalTheory.FrameDet.exists_lower
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:46.050421+00:00
-- url     : https://prove2.me/theorems/81756951-c301-4b44-8e39-26a6067071b4
-- title:
--   Frame Det: exists lower
-- statement:
--   The Frame Det construction uses the exists lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DetDvdEquivariantFramePolynomial.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/DetDvdEquivariantFramePolynomial.lean#L13-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DetDvdEquivariantFramePolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPolynomial Formalism.L2.LamCM
open GlobalTheory GlobalTheory.FrameDet
open GlobalTheory.BorelAlg

theorem GlobalTheory.FrameDet.exists_lower {K : Type} [Field K] {n : ℕ} (x y : Matrix (Fin n) (Fin n) K) (l : Fin n) (hl : ∀ i, i ≤ l)
    (hx : x.det ≠ 0) (h : ∀ i, i ≠ l → y i = x i) :
    ∃ b : Matrix (Fin n) (Fin n) K, y = b * x ∧ (∀ i j, i < j → b i j = 0) ∧ (∀ i, i ≠ l → b i i = 1) ∧
      b.det = b l l := by sorry
