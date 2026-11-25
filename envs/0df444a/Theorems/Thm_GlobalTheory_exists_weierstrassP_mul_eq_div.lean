-- Prove2me | Theorems.Thm_GlobalTheory_exists_weierstrassP_mul_eq_div
-- name    : GlobalTheory.exists_weierstrassP_mul_eq_div
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:20.588569+00:00
-- url     : https://prove2.me/theorems/ab14d7ab-0051-43aa-aad1-e8eb23e9db34
-- title:
--   Global Theory: exists weierstrass P mul eq div
-- statement:
--   The Global Theory construction uses the exists weierstrass P mul eq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L149-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsNumeratorOfInvolution.lean#L149-L245

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

theorem GlobalTheory.exists_weierstrassP_mul_eq_div (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
        L'.lattice.toAddSubgroup ∧
      D.natDegree + 1 = A.natDegree ∧
      (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
      ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z) := by sorry
