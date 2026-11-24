-- Prove2me | Theorems.Thm_GlobalTheory_rcout_ultra
-- name    : GlobalTheory.rcout_ultra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:57.447376+00:00
-- url     : https://prove2.me/theorems/1986e124-dded-4f84-92eb-d66e2e7fc8eb
-- title:
--   Global Theory: rcout ultra
-- statement:
--   The Global Theory construction uses the rcout ultra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L14-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NewtonPolygonDominantIndexXSubCMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.rcout_ultra {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) :
    ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by sorry
