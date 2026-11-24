-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_pair_fromRows
-- name    : GlobalTheory.FrameCompletion.pair_fromRows
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:04:58.052493+00:00
-- url     : https://prove2.me/theorems/0290908b-beba-44eb-8887-6453a33657d5
-- title:
--   Frame Completion: pair from Rows
-- statement:
--   The Frame Completion construction uses the pair from Rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L63-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}

theorem GlobalTheory.FrameCompletion.pair_fromRows {n : ℕ} {κ μ : Type} (C D : Matrix (Fin n) κ L) (C' D' : Matrix (Fin n) μ L) :
    cT σ (fromRows C D) * gramQ L n * fromRows C' D' =
      cT σ C * antiJ L n * C' - cT σ D * antiJ L n * D' := by sorry
