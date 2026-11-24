-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_injective_of_fderiv_ne_zero
-- name    : GlobalTheory.InjHol.injective_of_fderiv_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:03.357811+00:00
-- url     : https://prove2.me/theorems/7901d7a2-bd03-4e30-8739-b0df5a744389
-- title:
--   Inj Hol: injective of fderiv ne zero
-- statement:
--   The Inj Hol construction uses the injective of fderiv ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L252-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L252-L298

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

theorem GlobalTheory.InjHol.injective_of_fderiv_ne_zero {n : ℕ} (ih : LocalStatement n) {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hE : Module.finrank ℂ E = n + 1) (hF : Module.finrank ℂ F = n + 1) {f : E → F} {a : E}
    (hf : AnalyticAt ℂ f a) {s : Set E} (hs : s ∈ 𝓝 a) (hinj : InjOn f s)
    (h0 : fderiv ℂ f a ≠ 0) : Function.Injective (fderiv ℂ f a) := by sorry
