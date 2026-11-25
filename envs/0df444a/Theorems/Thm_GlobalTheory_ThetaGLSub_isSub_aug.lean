-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGLSub_isSub_aug
-- name    : GlobalTheory.ThetaGLSub.isSub_aug
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:41:32.84121+00:00
-- url     : https://prove2.me/theorems/1d88ef38-0632-5e74-a67e-c270e5df7b19
-- title:
--   Theta GLSub: is Sub aug
-- statement:
--   The Theta GLSub construction uses the is Sub aug property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L44-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L44-L56

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

theorem GlobalTheory.ThetaGLSub.isSub_aug (χ : GL (Fin n) k →* ℂˣ) : IsSub χ (aug m χ) := by sorry
