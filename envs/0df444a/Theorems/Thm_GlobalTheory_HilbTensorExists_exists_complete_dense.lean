-- Prove2me | Theorems.Thm_GlobalTheory_HilbTensorExists_exists_complete_dense
-- name    : GlobalTheory.HilbTensorExists.exists_complete_dense
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:21:33.095877+00:00
-- url     : https://prove2.me/theorems/55be885c-59e3-4878-a397-729dfa8b189c
-- title:
--   Hilb Tensor Exists: exists complete dense
-- statement:
--   The Hilb Tensor Exists construction uses the exists complete dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L38-L57

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsCompleteDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.HilbTensorExists

theorem GlobalTheory.HilbTensorExists.exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by sorry
