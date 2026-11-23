-- Prove2me | Theorems.Thm_GlobalTheory_AppellHumbert_eq_sum_re_im
-- name    : GlobalTheory.AppellHumbert.eq_sum_re_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:59:25.41124+00:00
-- url     : https://prove2.me/theorems/5a1839e9-918e-4acc-81ec-ace6c495c771
-- title:
--   Appell Humbert: eq sum re im
-- statement:
--   The Appell Humbert construction uses the eq sum re im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertNormalFormOfLinearExponent.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertNormalFormOfLinearExponent.lean#L29-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AppellHumbert
open Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.AppellHumbert.eq_sum_re_im {g : ℕ} (u : Fin g → ℂ) :
    u = ∑ j, ((u j).re • (Pi.single j (1 : ℂ) : Fin g → ℂ)
      + (u j).im • (Pi.single j I : Fin g → ℂ)) := by sorry
