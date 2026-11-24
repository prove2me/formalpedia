-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGLSub_om_sub
-- name    : GlobalTheory.ThetaGLSub.om_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:53.207948+00:00
-- url     : https://prove2.me/theorems/a54e125c-efdf-4d7a-9525-94709c94e06b
-- title:
--   Theta GLSub: om sub
-- statement:
--   The Theta GLSub construction uses the om sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L31-L33

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

theorem GlobalTheory.ThetaGLSub.om_sub (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Ψ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g h (Φ - Ψ) = om μ g h Φ - om μ g h Ψ := by sorry
