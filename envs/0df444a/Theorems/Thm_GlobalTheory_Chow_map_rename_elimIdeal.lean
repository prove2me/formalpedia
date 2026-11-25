-- Prove2me | Theorems.Thm_GlobalTheory_Chow_map_rename_elimIdeal
-- name    : GlobalTheory.Chow.map_rename_elimIdeal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:26.197411+00:00
-- url     : https://prove2.me/theorems/f29f8323-eb39-4a69-aabb-bdc3e50e43bf
-- title:
--   Chow: map rename elim Ideal
-- statement:
--   The Chow construction uses the map rename elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L107-L114

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
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]

theorem GlobalTheory.Chow.map_rename_elimIdeal (e : β ≃ β') (p : Ideal (MvPolynomial σ K)) :
    (elimIdeal β p).map (rename (Prod.map e id) : _ →ₐ[K] _) = elimIdeal β' p := by sorry
