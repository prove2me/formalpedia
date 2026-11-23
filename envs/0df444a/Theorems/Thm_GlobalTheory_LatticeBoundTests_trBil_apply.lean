-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBoundTests_trBil_apply
-- name    : GlobalTheory.LatticeBoundTests.trBil_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:55.783798+00:00
-- url     : https://prove2.me/theorems/b6967f33-80ab-4c40-8723-d32992cdd3c1
-- title:
--   Lattice Bound Tests: tr Bil apply
-- statement:
--   The Lattice Bound Tests construction uses the tr Bil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/JetSurvey/PremisesInhabited.lean#L28-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_PremisesInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBoundTests
open NumberField
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]

theorem GlobalTheory.LatticeBoundTests.trBil_apply (x y : 𝓞 E) :
    trBil E x y = ∑ σ : E →+* ℂ, (σ (x : E) * starRingEnd ℂ (σ (y : E))).re := by sorry
