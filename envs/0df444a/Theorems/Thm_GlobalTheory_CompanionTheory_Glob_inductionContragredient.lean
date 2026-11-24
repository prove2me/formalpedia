-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_inductionContragredient
-- name    : GlobalTheory.CompanionTheory.Glob.inductionContragredient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:49:53.532906+00:00
-- url     : https://prove2.me/theorems/7f3389d0-3195-4853-8465-65e01ad5f891
-- title:
--   Glob: induction Contragredient
-- statement:
--   The Glob construction uses the induction Contragredient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicInductionContragredient.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicInductionContragredient.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicInductionContragredient
import Theorems.Thm_GlobalTheory_SmGL_IndDual_inductionContragredient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob

theorem GlobalTheory.CompanionTheory.Glob.inductionContragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by sorry
