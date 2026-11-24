-- Prove2me | Theorems.Thm_GlobalTheory_taylorDir_sum
-- name    : GlobalTheory.taylorDir_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:13.838124+00:00
-- url     : https://prove2.me/theorems/0d862041-3570-496b-942a-800d923ee95e
-- title:
--   Global Theory: taylor Dir sum
-- statement:
--   The Global Theory construction uses the taylor Dir sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L303-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L303-L313

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}

theorem GlobalTheory.taylorDir_sum {κ : Type*} (s : Finset κ) {F : κ → W → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylorDir u (fun z => ∑ k ∈ s, F k z) = ∑ k ∈ s, taylorDir u (F k) := by sorry
