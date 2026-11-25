-- Prove2me | Theorems.Thm_GlobalTheory_taylor_sum
-- name    : GlobalTheory.taylor_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:05.86895+00:00
-- url     : https://prove2.me/theorems/de14e404-b953-4dab-91c0-a1b244650ee8
-- title:
--   Global Theory: taylor sum
-- statement:
--   The Global Theory construction uses the taylor sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L396-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L396-L398

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}

theorem GlobalTheory.taylor_sum {κ : Type*} (s : Finset κ) {F : κ → (σ → ℂ) → ℂ}
    (hF : ∀ k ∈ s, AnalyticAt ℂ (F k) 0) :
    taylor (fun z => ∑ k ∈ s, F k z) = ∑ k ∈ s, taylor (F k) := by sorry
