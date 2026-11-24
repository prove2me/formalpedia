-- Prove2me | Theorems.Thm_GlobalTheory_Chow_isPrime_elimIdeal
-- name    : GlobalTheory.Chow.isPrime_elimIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:49.632909+00:00
-- url     : https://prove2.me/theorems/c8bedb29-aca0-4dfc-af54-50b2e72c3c9f
-- title:
--   Chow: is Prime elim Ideal
-- statement:
--   The Chow construction uses the is Prime elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L245-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L245-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
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
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]

theorem GlobalTheory.Chow.isPrime_elimIdeal {p : Ideal (MvPolynomial σ K)} [p.IsPrime] (hp : ∃ j, X j ∉ p) :
    (elimIdeal β p).IsPrime := by sorry
