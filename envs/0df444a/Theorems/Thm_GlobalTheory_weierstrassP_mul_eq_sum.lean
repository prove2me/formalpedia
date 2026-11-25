-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_mul_eq_sum
-- name    : GlobalTheory.weierstrassP_mul_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:02:15.832026+00:00
-- url     : https://prove2.me/theorems/495fac25-d9a9-4dc4-afe7-c7aabf7387f4
-- title:
--   Global Theory: weierstrass P mul eq sum
-- statement:
--   The Global Theory construction uses the weierstrass P mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L91-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L91-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}

theorem GlobalTheory.weierstrassP_mul_eq_sum (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    {ι : Type*} [Fintype ι] (r : ι → ℂ) (h₁ : ∀ t, α * r t ∈ L'.lattice)
    (h₂ : ∀ s t, r s - r t ∈ L.lattice → s = t)
    (h₃ : ∀ m, α * m ∈ L'.lattice → ∃ t, m - r t ∈ L.lattice) (z : ℂ) :
    α ^ 2 * ℘[L'] (α * z) = ∑ t, (℘[L] (z - r t) - ℘[L] (r t)) := by sorry
