-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_riemannTheta_comp
-- name    : GlobalTheory.differentiableOn_riemannTheta_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:48.272723+00:00
-- url     : https://prove2.me/theorems/f10be609-4c43-4674-9cfd-a5ab69ad06f2
-- title:
--   Global Theory: differentiable On riemann Theta comp
-- statement:
--   The Global Theory construction uses the differentiable On riemann Theta comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L70-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.differentiableOn_riemannTheta_comp (a b : ι → ℝ) {Ω : E → Matrix ι ι ℂ} {v : E → ι → ℂ}
    {U : Set E} (h : ∀ x ∈ U, IsSiegel (Ω x)) (hΩ : ∀ i j, DifferentiableOn ℂ (fun y => Ω y i j) U)
    (hv : DifferentiableOn ℂ v U) :
    DifferentiableOn ℂ (fun y => riemannTheta a b (Ω y) (v y)) U := by sorry
