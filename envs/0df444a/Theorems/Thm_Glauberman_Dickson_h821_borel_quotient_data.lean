-- Prove2me | Theorems.Thm_Glauberman_Dickson_h821_borel_quotient_data
-- name    : Glauberman.Dickson.h821_borel_quotient_data
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:37:23.18559+00:00
-- url     : https://prove2.me/theorems/7f932ff3-d79a-40ea-97e5-9bb1ecb5a905
-- title:
--   The cyclic quotient and explicit torus data of a Sylow normalizer in PSL₂
-- statement:
--   For a nontrivial Sylow p-subgroup P of H ≤ PSL₂(F), where F is a finite field of cardinality p^f, the normalizer N modulo its normal subgroup P is cyclic and its order divides the split torus order. Nonidentity quotient representatives act without nontrivial fixed points on P. After an inner conjugation of H, its normalizer lies in the standard unipotent-by-diagonal Borel subgroup. The theorem retains the explicit injective unipotent character, split-torus homomorphism and matrix/conjugation formulas from Huppert II.8.21.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonSylowNormalizer.lean; declaration Glauberman.Dickson.h821_borel_quotient_data. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.h821_borel_quotient_data
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (P : Sylow p H) (hP_ne_bot : (P : Subgroup H) ≠ ⊥)
    (N : Subgroup H) (hN : N = Subgroup.normalizer (P : Set H))
    (PN : Subgroup N) [PN.Normal]
    (hPN : PN = (P : Subgroup H).subgroupOf N) :
    IsCyclic (N ⧸ PN) ∧
      Nat.card (N ⧸ PN) ∣
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      (∀ n : N, n ∉ PN → ∀ x : (P : Subgroup H), x ≠ 1 →
        (n : H) * (x : H) * (n : H)⁻¹ ≠ (x : H)) ∧
      ∃ U T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
        ∃ conjH : H →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
          Function.Injective conjH ∧
          (∃ g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, ∀ h : H,
            conjH h = g * (h : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * g⁻¹) ∧
          IsMulCommutative U ∧
          IsCyclic T ∧
          Nat.card T =
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
          (∀ t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, t ∈ T →
            ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, x ∈ U →
              t * x * t⁻¹ = x → t = 1 ∨ x = 1) ∧
          (P : Subgroup H).map conjH ≤ U ∧
          U ⊔ T ≤ Subgroup.normalizer
            (U : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ∧
          (∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, x ∈ U ⊔ T → x ∉ U →
            ∃ u : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, u ∈ U ∧
              x ∈ T.map (MulAut.conj u).toMonoidHom) ∧
          (∀ n : N, conjH (n : H) ∈ U ⊔ T) ∧
          (∀ n : N, conjH (n : H) ∈ U ↔ n ∈ PN) ∧
          ∃ unipotent : AddChar F (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
            ∃ splitTorus : Fˣ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F,
              Function.Injective unipotent ∧
              U = unipotent.toMonoidHom.range ∧
              T = splitTorus.range ∧
              (∀ a : Fˣ, ∀ x : F,
                splitTorus a * unipotent x * (splitTorus a)⁻¹ =
                  unipotent ((a : F) ^ 2 * x)) ∧
              (∀ x : F, unipotent x =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F)) ∧
              ∀ a : Fˣ, splitTorus a =
                QuotientGroup.mk'
                  (Subgroup.center
                    (Matrix.SpecialLinearGroup (Fin 2) F))
                  (⟨!![(a : F), 0; 0, (a⁻¹ : F)],
                      by simp [Matrix.det_fin_two]⟩ :
                    Matrix.SpecialLinearGroup (Fin 2) F) := by sorry
