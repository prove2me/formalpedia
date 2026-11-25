-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_det_homog
-- name    : GlobalTheory.DiagBlock.det_homog
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:11.614071+00:00
-- url     : https://prove2.me/theorems/34b9b83c-8f5c-4423-94a1-43936eaac40d
-- title:
--   Diag Block: det homog
-- statement:
--   The Diag Block construction uses the det homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L216-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L216-L229

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock

theorem GlobalTheory.DiagBlock.det_homog {C : Type} [Field C] {σ : Type} {n : ℕ} (w : σ → ℕ) (f : Fin n → Fin n → σ)
    (r : Fin n → ℕ) (h : ∀ b c, w (f b c) = r b) :
    (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (f b c) : MvPolynomial σ C)).det.IsWeightedHomogeneous w (∑ b, r b) := by sorry
