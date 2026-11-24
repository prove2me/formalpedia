-- Prove2me | Theorems.Thm_GlobalTheory_rcout_coeff_zero
-- name    : GlobalTheory.rcout_coeff_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:16:44.258178+00:00
-- url     : https://prove2.me/theorems/dcabae49-b967-43a0-935d-4d328c3c6fec
-- title:
--   Global Theory: rcout coeff zero
-- statement:
--   The Global Theory construction uses the rcout coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NewtonPolygonDominantIndexXSubCMul.lean#L10-L12

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

theorem GlobalTheory.rcout_coeff_zero {K : Type} [NormedField K] (g : K[X]) (a : K) :
    ((X - C a) * g).coeff 0 = -(a * g.coeff 0) := by sorry
