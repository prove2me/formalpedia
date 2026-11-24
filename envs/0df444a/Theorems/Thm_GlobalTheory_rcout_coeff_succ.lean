-- Prove2me | Theorems.Thm_GlobalTheory_rcout_coeff_succ
-- name    : GlobalTheory.rcout_coeff_succ
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:51.278505+00:00
-- url     : https://prove2.me/theorems/fe4b3cfe-fc1e-45bd-986d-2ec52b092d39
-- title:
--   Global Theory: rcout coeff succ
-- statement:
--   The Global Theory construction uses the rcout coeff succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L6-L8

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

theorem GlobalTheory.rcout_coeff_succ {K : Type} [NormedField K] (g : K[X]) (a : K) (k : ℕ) :
    ((X - C a) * g).coeff (k + 1) = g.coeff k - a * g.coeff (k + 1) := by sorry
