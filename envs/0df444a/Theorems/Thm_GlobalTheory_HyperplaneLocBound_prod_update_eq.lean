-- Prove2me | Theorems.Thm_GlobalTheory_HyperplaneLocBound_prod_update_eq
-- name    : GlobalTheory.HyperplaneLocBound.prod_update_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:13:06.885348+00:00
-- url     : https://prove2.me/theorems/44cda571-90a8-4d3e-8bd7-68c664e3563b
-- title:
--   Hyperplane Loc Bound: prod update eq
-- statement:
--   The Hyperplane Loc Bound construction uses the prod update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocallyBoundedOffCoordinateHyperplanes.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocallyBoundedOffCoordinateHyperplanes.lean#L16-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocallyBoundedOffCoordinateHyperplanes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory GlobalTheory.HyperplaneLocBound

theorem GlobalTheory.HyperplaneLocBound.prod_update_eq {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℕ) (k : Fin n) (t : ℂ) :
    ∏ j, ‖Function.update z k t j‖ ^ m j =
      ‖t‖ ^ m k * ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j := by sorry
