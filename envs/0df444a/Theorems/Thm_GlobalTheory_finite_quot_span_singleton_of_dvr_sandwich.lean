-- Prove2me | Theorems.Thm_GlobalTheory_finite_quot_span_singleton_of_dvr_sandwich
-- name    : GlobalTheory.finite_quot_span_singleton_of_dvr_sandwich
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:04.999764+00:00
-- url     : https://prove2.me/theorems/988349d2-2804-4e22-a5fb-62634ba90f93
-- title:
--   Global Theory: finite quot span singleton of dvr sandwich
-- statement:
--   The Global Theory construction uses the finite quot span singleton of dvr sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelf.lean#L6-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FiniteSubmodulesBetweenSmulAndSelf.lean#L6-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteSubmodulesBetweenSmulAndSelf
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

theorem GlobalTheory.finite_quot_span_singleton_of_dvr_sandwich (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [hF : Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) := by sorry
