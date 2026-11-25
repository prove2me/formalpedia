-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_bijective_fderiv_of_injOn
-- name    : GlobalTheory.InjHol.bijective_fderiv_of_injOn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:29.899408+00:00
-- url     : https://prove2.me/theorems/dd3a345b-20ca-41fe-b3af-e1b4418137da
-- title:
--   Inj Hol: bijective fderiv of inj On
-- statement:
--   The Inj Hol construction uses the bijective fderiv of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L368-L376
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L368-L376

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol

theorem GlobalTheory.InjHol.bijective_fderiv_of_injOn :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → (Fin n → ℂ)), IsOpen U →
      DifferentiableOn ℂ f U → Set.InjOn f U → ∀ a ∈ U, Function.Bijective (fderiv ℂ f a) := by sorry
