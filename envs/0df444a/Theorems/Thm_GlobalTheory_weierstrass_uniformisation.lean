-- Prove2me | Theorems.Thm_GlobalTheory_weierstrass_uniformisation
-- name    : GlobalTheory.weierstrass_uniformisation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:10:02.867349+00:00
-- url     : https://prove2.me/theorems/7c83ebd8-9ccb-4400-851e-5d72f1e176c2
-- title:
--   Global Theory: weierstrass uniformisation
-- statement:
--   The Global Theory construction uses the weierstrass uniformisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L225-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean#L225-L268

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

theorem GlobalTheory.weierstrass_uniformisation :
    (∀ L : PeriodPair, (latticeCurve L).IsElliptic) ∧
    (∀ L : PeriodPair, ∃ e : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (latticeCurve L).toAffine.Point,
      ∀ z ∉ L.lattice, ∃ h, e (z : ℂ ⧸ L.lattice.toAddSubgroup) =
        .some (℘[L] z) (℘'[L] z / 2) h) ∧
    (∀ L : PeriodPair, (∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧
        ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) ∧
      ∀ (a : ℂ) (τ : ℍ), a ≠ 0 → (∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) →
        (latticeCurve L).j = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) ∧
    (∀ (L L' : PeriodPair) (α : ℂ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L'.lattice) →
      ∃ A D : ℂ[X],
        (∀ i, A.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        (∀ i, D.coeff i ∈ Subfield.closure
          ({L.g₂, L.g₃, α} ∪ ℘[L] '' {t | t ∉ L.lattice ∧ α * t ∈ L'.lattice})) ∧
        D.Monic ∧ A.leadingCoeff = (α ^ 2)⁻¹ ∧ IsCoprime A D ∧
        A.natDegree = (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
          L'.lattice.toAddSubgroup ∧
        D.natDegree + 1 = A.natDegree ∧
        (∀ z ∉ L.lattice, D.eval (℘[L] z) = 0 ↔ α * z ∈ L'.lattice) ∧
        ∀ z, α * z ∉ L'.lattice → ℘[L'] (α * z) = A.eval (℘[L] z) / D.eval (℘[L] z)) ∧
    (∀ (L : PeriodPair) (f : ℂ → ℂ), Meromorphic f → (∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) →
      (∀ z, f (-z) = f z) →
      ∃ A D : ℂ[X], D.Monic ∧ ∀ z ∉ L.lattice, f z * D.eval (℘[L] z) = A.eval (℘[L] z)) ∧
    (∀ (W : WeierstrassCurve ℂ) [W.IsElliptic],
      ∃ (L : PeriodPair) (C : VariableChange ℂ), C • W = latticeCurve L) ∧
    (∀ (L L' : PeriodPair)
      (φ : (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point) (A B D : ℂ[X]),
      D ≠ 0 → (∀ x y h, D.eval x ≠ 0 →
        ∃ y' h', φ (.some x y h) = .some ((A.eval x + B.eval x * y) / D.eval x) y' h') →
      ∃ α : ℂ, α ≠ 0 ∧ (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧
        ∀ z, φ (latticePoint L z) = latticePoint L' (α * z)) := by sorry
