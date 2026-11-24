-- Prove2me | Theorems.Thm_GlobalTheory_InjHol_exists_slice
-- name    : GlobalTheory.InjHol.exists_slice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:12:13.607981+00:00
-- url     : https://prove2.me/theorems/9406dfd4-4693-4cfe-b585-b1ec0351ce5a
-- title:
--   Inj Hol: exists slice
-- statement:
--   The Inj Hol construction uses the exists slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L98-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean#L98-L139

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

theorem GlobalTheory.InjHol.exists_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : E → ℂ} {b : E} (hg : AnalyticAt ℂ g b) {L : E →L[ℂ] ℂ} (hL : HasFDerivAt g L b)
    (h0 : L ≠ 0) :
    ∃ ψ : L.ker → E, AnalyticAt ℂ ψ 0 ∧ ψ 0 = b ∧ HasFDerivAt ψ L.ker.subtypeL 0 ∧
      (∀ᶠ x in 𝓝 0, g (ψ x) = g b) ∧ ∃ s ∈ 𝓝 (0 : L.ker), InjOn ψ s := by sorry
