-- Prove2me | Theorems.Thm_GlobalTheory_Chow_forall_aeval_eq_zero_iff
-- name    : GlobalTheory.Chow.forall_aeval_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:59.971507+00:00
-- url     : https://prove2.me/theorems/57b34647-aefb-48ae-8179-70dfc9a151de
-- title:
--   Chow: forall aeval eq zero iff
-- statement:
--   The Chow construction uses the forall aeval eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L165-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/AevalEqZeroOfHomogeneousComponent.lean#L165-L205

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
variable {K : Type*} [CommRing K] {σ β : Type*}

theorem GlobalTheory.Chow.forall_aeval_eq_zero_iff [Fintype σ] {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    (t : β × σ → Ω) :
    (∀ f ∈ elimIdeal β p, aeval t f = 0) ↔
      ∃ x : σ → Ω, x ≠ 0 ∧ (∀ g ∈ p, aeval x g = 0) ∧ ∀ i, ∑ j, t (i, j) * x j = 0 := by sorry
