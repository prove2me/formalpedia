-- Prove2me | Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_aeval_smul
-- name    : GlobalTheory.Chow.IsBlockHomogeneous.aeval_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:15.001582+00:00
-- url     : https://prove2.me/theorems/9c654794-00e2-57ec-ba36-455ce0ed92eb
-- title:
--   Is Block Homogeneous: aeval smul
-- statement:
--   The Is Block Homogeneous construction uses the aeval smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L319-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L319-L328

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
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']

theorem GlobalTheory.Chow.IsBlockHomogeneous.aeval_smul [Fintype σ] [Fintype β] {G : Type*} [CommRing G]
    [Algebra K G] {f : MvPolynomial (β × σ) K} {a : β → ℕ} (h : IsBlockHomogeneous f a)
    (c : β → G) (t : β × σ → G) :
    aeval (fun v => c v.1 * t v) f = (∏ i, c i ^ a i) * aeval t f := by sorry
