-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoDY_norm_igE_le
-- name    : GlobalTheory.HeckeTwoDY.norm_igE_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:40.753802+00:00
-- url     : https://prove2.me/theorems/04aa8cb9-2888-466f-bf30-30b64ee15989
-- title:
--   Hecke Two DY: norm ig E le
-- statement:
--   The Hecke Two DY construction uses the norm ig E le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L157-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABHasDerivAtY.lean#L157-L173

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

theorem GlobalTheory.HeckeTwoDY.norm_igE_le {a b : ℕ} {σ : ℂ} {ν y y' : ℝ} (hk : 0 ≤ (a : ℝ) + b + 2 * σ.re) (hy : y ≠ 0)
    (hy' : |y' - y| < |y| / 2) (t : ℝ) :
    ‖igE a b σ ν y' t‖ ≤ Real.exp (-(((a : ℝ) + b + 2 * σ.re) / 2) * Real.log (t ^ 2 + (y / 2) ^ 2)) := by sorry
