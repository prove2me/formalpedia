-- Prove2me | Theorems.Thm_GlobalTheory_AffinePoints_norm_le_of_isRoot_monic
-- name    : GlobalTheory.AffinePoints.norm_le_of_isRoot_monic
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:54:34.107662+00:00
-- url     : https://prove2.me/theorems/31d771b1-6253-4c8e-bf1c-f485b49b3374
-- title:
--   Affine Points: norm le of is Root monic
-- statement:
--   The Affine Points construction uses the norm le of is Root monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L59-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsApplyEqZeroAndEqOne.lean#L59-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ContinuousAevalMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsApplyEqZeroAndEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffinePoints
open Topology Filter Set Polynomial
variable {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

theorem GlobalTheory.AffinePoints.norm_le_of_isRoot_monic {h : ℂ[X]} (hm : h.Monic) {t : ℂ} (ht : h.IsRoot t) :
    ‖t‖ ≤ ∑ i ∈ Finset.range h.natDegree, ‖h.coeff i‖ + 1 := by sorry
