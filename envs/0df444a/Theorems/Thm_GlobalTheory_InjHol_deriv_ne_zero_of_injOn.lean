-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_deriv_ne_zero_of_injOn
-- name    : GlobalTheory.InjHol.deriv_ne_zero_of_injOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:13.306325+00:00
-- url     : https://prove2.me/theorems/0ff3431e-a038-48b1-bc47-d590bb7affdf
-- title:
--   Inj Hol: deriv ne zero of inj On
-- statement:
--   The Inj Hol construction uses the deriv ne zero of inj On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L43-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L43-L88

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

theorem GlobalTheory.InjHol.deriv_ne_zero_of_injOn {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {s : Set ℂ}
    (hs : s ∈ 𝓝 a) (hinj : InjOn f s) : deriv f a ≠ 0 := by sorry
