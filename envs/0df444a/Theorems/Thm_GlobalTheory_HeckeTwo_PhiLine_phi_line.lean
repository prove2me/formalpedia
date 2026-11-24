-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_PhiLine_phi_line
-- name    : GlobalTheory.HeckeTwo.PhiLine.phi_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:07.624805+00:00
-- url     : https://prove2.me/theorems/ac2ecdb3-54b8-4e18-83b6-3c62c9a001a3
-- title:
--   Phi Line: phi line
-- statement:
--   The Phi Line construction uses the phi line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoKernelPhiLineContinuousIntegrable.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeWeightTwoKernelPhiLineContinuousIntegrable.lean#L47-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.PhiLine

theorem GlobalTheory.HeckeTwo.PhiLine.phi_line (σ : ℂ) (hσ : 0 < σ.re) (y : ℝ) (hy : y ≠ 0) :
    Continuous (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) ∧
      MeasureTheory.Integrable (fun t : ℝ => GlobalTheory.HeckeTwo.phi σ ((t : ℂ) + (y : ℂ) * Complex.I)) := by sorry
