-- Prove2me | Theorems.Thm_GlobalTheory_HilbTensorExists_exists_isHilbTensor
-- name    : GlobalTheory.HilbTensorExists.exists_isHilbTensor
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:29:21.239082+00:00
-- url     : https://prove2.me/theorems/6c4d383c-148b-4059-b0c7-67574edb1318
-- title:
--   Hilb Tensor Exists: exists is Hilb Tensor
-- statement:
--   The Hilb Tensor Exists construction uses the exists is Hilb Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L80-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsCompleteDense.lean#L80-L97

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

theorem GlobalTheory.HilbTensorExists.exists_isHilbTensor (I : AutInst) (H : NumberField.InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (hσ : ∀ v (g : Formalism.REAL.UJ (I.ε v)) x y, ⟪σ v (uMat g) x, σ v (uMat g) y⟫_ℂ = ⟪x, y⟫_ℂ) :
    ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens := by sorry
