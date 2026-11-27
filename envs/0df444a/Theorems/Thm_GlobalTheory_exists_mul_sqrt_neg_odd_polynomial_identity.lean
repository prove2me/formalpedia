-- Prove2me | Theorems.Thm_GlobalTheory_exists_mul_sqrt_neg_odd_polynomial_identity
-- name    : GlobalTheory.exists_mul_sqrt_neg_odd_polynomial_identity
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:27.027892+00:00
-- url     : https://prove2.me/theorems/4c5e85fc-d137-415a-a24a-5be96b18a5e5
-- title:
--   Global Theory: exists mul sqrt neg odd polynomial identity
-- statement:
--   The Global Theory construction uses the exists mul sqrt neg odd polynomial identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulSqrtNegOddPolynomialIdentity.lean#L18-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsMulSqrtNegOddPolynomialIdentity.lean#L18-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulSqrtNegOddPolynomialIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial PeriodPair
open GlobalTheory

theorem GlobalTheory.exists_mul_sqrt_neg_odd_polynomial_identity (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by sorry
