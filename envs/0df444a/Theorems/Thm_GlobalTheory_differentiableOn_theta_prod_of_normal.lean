-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_theta_prod_of_normal
-- name    : GlobalTheory.differentiableOn_theta_prod_of_normal
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:36.228813+00:00
-- url     : https://prove2.me/theorems/fc883ca5-9eff-4a2b-9be7-c4f3f7422d2a
-- title:
--   Global Theory: differentiable On theta prod of normal
-- statement:
--   The Global Theory construction uses the differentiable On theta prod of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnThetaProdOfNormal.lean#L17-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnThetaProdOfNormal.lean#L17-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta
open GlobalTheory

theorem GlobalTheory.differentiableOn_theta_prod_of_normal {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by sorry
