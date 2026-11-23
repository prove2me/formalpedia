-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoDY_continuous_igE
-- name    : GlobalTheory.HeckeTwoDY.continuous_igE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:13.206899+00:00
-- url     : https://prove2.me/theorems/2160323a-368d-441b-8246-868b57e4d10b
-- title:
--   Hecke Two DY: continuous ig E
-- statement:
--   The Hecke Two DY construction uses the continuous ig E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L139-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L139-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtY
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
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoDY
open MeasureTheory

theorem GlobalTheory.HeckeTwoDY.continuous_igE (a b : ℕ) (σ : ℂ) (ν : ℝ) {y : ℝ} (hy : y ≠ 0) : Continuous (fun t => igE a b σ ν y t) := by sorry
