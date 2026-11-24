-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGLSub_aug_le_SB
-- name    : GlobalTheory.ThetaGLSub.aug_le_SB
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:09.734333+00:00
-- url     : https://prove2.me/theorems/8be0f937-1266-4fa0-aac1-0b3c78294e93
-- title:
--   Theta GLSub: aug le SB
-- statement:
--   The Theta GLSub construction uses the aug le SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L39-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSubAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.ThetaGLSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable {m : ℕ}

theorem GlobalTheory.ThetaGLSub.aug_le_SB (χ : GL (Fin n) k →* ℂˣ) : aug m χ ≤ SB (Matrix (Fin n) (Fin m) k) := by sorry
