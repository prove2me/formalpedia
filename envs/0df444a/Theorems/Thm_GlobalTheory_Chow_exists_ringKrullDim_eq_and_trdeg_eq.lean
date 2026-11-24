-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_ringKrullDim_eq_and_trdeg_eq
-- name    : GlobalTheory.Chow.exists_ringKrullDim_eq_and_trdeg_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:05.307887+00:00
-- url     : https://prove2.me/theorems/6b1a44d2-a743-40dd-be0b-2c635ac6bd2b
-- title:
--   Chow: exists ring Krull Dim eq and trdeg eq
-- statement:
--   The Chow construction uses the exists ring Krull Dim eq and trdeg eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsAlgebraicIndependentGenericPoint.lean#L29-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.Chow.exists_ringKrullDim_eq_and_trdeg_eq (K A : Type u) [Field K] [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] :
    ∃ s : ℕ, ringKrullDim A = s ∧ Algebra.trdeg K A = s := by sorry
