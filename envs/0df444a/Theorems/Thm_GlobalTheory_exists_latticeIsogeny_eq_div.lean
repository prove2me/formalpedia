-- Prove2me | Theorems.Thm_GlobalTheory_exists_latticeIsogeny_eq_div
-- name    : GlobalTheory.exists_latticeIsogeny_eq_div
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:53.189583+00:00
-- url     : https://prove2.me/theorems/85016822-6f75-40cd-b60f-96e813d15b67
-- title:
--   Global Theory: exists lattice Isogeny eq div
-- statement:
--   The Global Theory construction uses the exists lattice Isogeny eq div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L64-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L64-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}

theorem GlobalTheory.exists_latticeIsogeny_eq_div (hα0 : α ≠ 0) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice)
    (k : Subfield ℂ) (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L'.lattice → ℘[L] t ∈ k) :
    ∃ A D : ℂ[X], (∀ i, A.coeff i ∈ k) ∧ (∀ i, D.coeff i ∈ k) ∧ D.Monic ∧
      A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
      A.natDegree = Nat.card (latticeIsogeny α hα).ker ∧ D.natDegree + 1 = A.natDegree ∧
      ∀ (x y : ℂ) (h : (latticeCurve L).toAffine.Nonsingular x y),
        (D.eval x = 0 → latticeIsogeny α hα (.some x y h) = 0) ∧
        (D.eval x ≠ 0 → ∃ h', latticeIsogeny α hα (.some x y h) = .some (A.eval x / D.eval x)
          (α⁻¹ * ((derivative A * D - A * derivative D).eval x / D.eval x ^ 2) * y) h') := by sorry
