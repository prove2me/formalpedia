-- Prove2me | Theorems.Thm_GlobalTheory_Chow_exists_smul_mem_of_span_eq_top
-- name    : GlobalTheory.Chow.exists_smul_mem_of_span_eq_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:10:02.704987+00:00
-- url     : https://prove2.me/theorems/51134c9d-aa35-4c66-86ad-e70831b31ae1
-- title:
--   Chow: exists smul mem of span eq top
-- statement:
--   The Chow construction uses the exists smul mem of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L12-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L12-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
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
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.Chow.exists_smul_mem_of_span_eq_top {R Ω n : Type*} [CommRing R] [Field Ω] [Finite n]
    (φ : R →+* Ω) (S : Submodule R (n → R))
    (h : Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S) = ⊤) :
    ∃ r, φ r ≠ 0 ∧ ∀ w, r • w ∈ S := by sorry
