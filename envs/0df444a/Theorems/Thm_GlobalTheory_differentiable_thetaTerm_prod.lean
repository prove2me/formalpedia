-- Prove2me | Theorems.Thm_GlobalTheory_differentiable_thetaTerm_prod
-- name    : GlobalTheory.differentiable_thetaTerm_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:15.912902+00:00
-- url     : https://prove2.me/theorems/a682e41a-361f-4abd-bc91-ef1d654ed32e
-- title:
--   Global Theory: differentiable theta Term prod
-- statement:
--   The Global Theory construction uses the differentiable theta Term prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnThetaProdOfNormal.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/DifferentiableOnThetaProdOfNormal.lean#L10-L15

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

theorem GlobalTheory.differentiable_thetaTerm_prod {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by sorry
