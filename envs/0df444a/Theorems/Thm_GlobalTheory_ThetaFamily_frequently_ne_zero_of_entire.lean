-- Prove2me | Theorems.Thm_GlobalTheory_ThetaFamily_frequently_ne_zero_of_entire
-- name    : GlobalTheory.ThetaFamily.frequently_ne_zero_of_entire
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:05:46.287929+00:00
-- url     : https://prove2.me/theorems/8e8695cf-aeb9-4abb-80cb-b66e531f1341
-- title:
--   Theta Family: frequently ne zero of entire
-- statement:
--   The Theta Family construction uses the frequently ne zero of entire property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfFiniteOfClosedFibres.lean#L112-L117

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory GlobalTheory.ThetaFamily

theorem GlobalTheory.ThetaFamily.frequently_ne_zero_of_entire {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {θ : E → ℂ} (hd : Differentiable ℂ θ) (h0 : θ ≠ 0) (z : E) : ∃ᶠ w in 𝓝 z, θ w ≠ 0 := by sorry
