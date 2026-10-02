-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_27_dickson_psl2_subgroup_classification
-- name    : Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T14:02:31.162571+00:00
-- url     : https://prove2.me/theorems/ccda8db9-ea6e-4448-8698-51792143e58e
-- title:
--   Dickson’s subgroup classification for finite PSL₂
-- statement:
--   For a finite field F of cardinality p^f and a subgroup H of PSL₂(F), one of nine explicit alternatives holds: elementary abelian, cyclic, dihedral, A₄, S₄, A₅, elementary-abelian-by-cyclic, a PSL₂ subfield group, or a PGL₂ subfield group. All torus-order divisibilities, exceptional characteristic restrictions and subfield exponent divisibilities are retained exactly from the public Huppert II.8.27 statement.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean; declaration Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Definitions.Def_cfsg_elementary_abelian
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    IsElementaryAbelian p H ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = z ∧ IsCyclic H) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧ Nonempty (H ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup H,
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) := by sorry
