-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint_eq_zero_iff
-- name    : GlobalTheory.Chow.aeval_genericPoint_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:44.074316+00:00
-- url     : https://prove2.me/theorems/f5769477-ca02-42e6-822a-f811366a18b6
-- title:
--   Chow: aeval generic Point eq zero iff
-- statement:
--   The Chow construction uses the aeval generic Point eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L234-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L234-L236

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
omit [Fintype σ]

theorem GlobalTheory.Chow.aeval_genericPoint_eq_zero_iff (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = 0 ↔ g ∈ p := by sorry
