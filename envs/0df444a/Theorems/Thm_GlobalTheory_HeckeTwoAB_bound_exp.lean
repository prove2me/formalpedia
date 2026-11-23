-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoAB_bound_exp
-- name    : GlobalTheory.HeckeTwoAB.bound_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:49.295589+00:00
-- url     : https://prove2.me/theorems/ff4f41b3-624e-404e-805c-3b91c94015c0
-- title:
--   Hecke Two AB: bound exp
-- statement:
--   The Hecke Two AB construction uses the bound exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeHankelTransformABDifferentiableOnSigma.lean#L72-L80

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
open GlobalTheory GlobalTheory.HeckeTwoAB
open MeasureTheory GlobalTheory.HeckeTwoC

theorem GlobalTheory.HeckeTwoAB.bound_exp {ε M c L0 D : ℝ} (hc : 1 + 2 * ε ≤ c) (hM : c ≤ M) (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.exp (-c * (L0 + D)) ≤ Real.exp (M * |L0|) * Real.exp (-(1 + ε) * D) * Real.exp (-(ε * D)) := by sorry
