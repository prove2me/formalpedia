-- Prove2me | Theorems.Thm_GlobalTheory_HilbTensorExists_exists_pre
-- name    : GlobalTheory.HilbTensorExists.exists_pre
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:21:32.430827+00:00
-- url     : https://prove2.me/theorems/0dabdc12-47b0-4b72-abd4-a3e99b6c81d9
-- title:
--   Hilb Tensor Exists: exists pre
-- statement:
--   The Hilb Tensor Exists construction uses the exists pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L28-L36

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

theorem GlobalTheory.HilbTensorExists.exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by sorry
