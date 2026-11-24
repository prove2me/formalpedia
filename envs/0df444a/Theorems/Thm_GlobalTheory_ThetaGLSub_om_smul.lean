-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGLSub_om_smul
-- name    : GlobalTheory.ThetaGLSub.om_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:06:00.275142+00:00
-- url     : https://prove2.me/theorems/e88ba3fc-9f8f-4171-84da-de3ca1e22297
-- title:
--   Theta GLSub: om smul
-- statement:
--   The Theta GLSub construction uses the om smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L27-L29

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

theorem GlobalTheory.ThetaGLSub.om_smul (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (c : ℂ) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (c • Φ) = c • om μ g h Φ := by sorry
