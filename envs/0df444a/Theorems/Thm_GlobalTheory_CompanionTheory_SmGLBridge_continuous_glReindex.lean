-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmGLBridge_continuous_glReindex
-- name    : GlobalTheory.CompanionTheory.SmGLBridge.continuous_glReindex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:55.633012+00:00
-- url     : https://prove2.me/theorems/4c8fb13f-f045-50c4-9325-bddd3a4faa98
-- title:
--   Sm GLBridge: continuous gl Reindex
-- statement:
--   The Sm GLBridge construction uses the continuous gl Reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IrreducibleSmoothAdmissibleGL.lean#L17-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmGLBridge
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

theorem GlobalTheory.CompanionTheory.SmGLBridge.continuous_glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) : Continuous (glReindex (k := k) e) := by sorry
