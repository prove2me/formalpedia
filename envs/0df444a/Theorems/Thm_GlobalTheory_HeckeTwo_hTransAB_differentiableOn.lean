-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_hTransAB_differentiableOn
-- name    : GlobalTheory.HeckeTwo.hTransAB_differentiableOn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:13:08.080786+00:00
-- url     : https://prove2.me/theorems/6fac06ed-967a-45a4-bf21-55375a645436
-- title:
--   Hecke Two: h Trans AB differentiable On
-- statement:
--   The Hecke Two construction uses the h Trans AB differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L163-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L163-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
open MeasureTheory GlobalTheory.HeckeTwoC GlobalTheory.HeckeTwoAB

theorem GlobalTheory.HeckeTwo.hTransAB_differentiableOn : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 →
    DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by sorry
