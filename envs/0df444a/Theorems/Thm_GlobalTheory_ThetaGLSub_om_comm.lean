-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGLSub_om_comm
-- name    : GlobalTheory.ThetaGLSub.om_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:00.587048+00:00
-- url     : https://prove2.me/theorems/32596e6d-f174-47f1-8fe4-4b3f6a3978e9
-- title:
--   Theta GLSub: om comm
-- statement:
--   The Theta GLSub construction uses the om comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsSubAug.lean#L35-L37

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

theorem GlobalTheory.ThetaGLSub.om_comm (μ : kˣ →* ℂˣ) (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ : Matrix (Fin n) (Fin m) k → ℂ) :
    om μ g 1 (om μ 1 h Φ) = om μ 1 h (om μ g 1 Φ) := by sorry
