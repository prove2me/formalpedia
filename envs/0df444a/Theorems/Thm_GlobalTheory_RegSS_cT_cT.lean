-- Prove2me | Theorems.Thm_GlobalTheory_RegSS_cT_cT
-- name    : GlobalTheory.RegSS.cT_cT
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:24:49.479797+00:00
-- url     : https://prove2.me/theorems/64f42d47-2081-5beb-8f92-d833dff62214
-- title:
--   Reg SS: c T c T
-- statement:
--   The Reg SS construction uses the c T c T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L303-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NotCompactOfIdempotent.lean#L303-L304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.RegSS.cT_cT (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) (a : Matrix n n A) : cT σ (cT σ a) = a := by sorry
