-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_not_injOn_of_fderiv_eq_zero
-- name    : GlobalTheory.InjHol.not_injOn_of_fderiv_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:47.314991+00:00
-- url     : https://prove2.me/theorems/a37cfba9-111f-435c-93c4-cc4bb77a3548
-- title:
--   Inj Hol: not inj On of fderiv eq zero
-- statement:
--   The Inj Hol construction uses the not inj On of fderiv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L27-L41

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

theorem GlobalTheory.InjHol.not_injOn_of_fderiv_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] [Nontrivial E] {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) (h0 : ∀ᶠ x in 𝓝 a, fderiv ℂ f x = 0) {s : Set E} (hs : s ∈ 𝓝 a) :
    ¬ InjOn f s := by sorry
