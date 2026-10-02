-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_26_dickson_case_p_part_normalizer_large
-- name    : Glauberman.Dickson.huppert_II_8_26_dickson_case_p_part_normalizer_large
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:49:46.755197+00:00
-- url     : https://prove2.me/theorems/1905fd91-86c3-40bd-8973-cc237fb2b0ed
-- title:
--   Dickson’s branch with a larger Sylow normalizer
-- statement:
--   Let F have cardinality p^f with p prime, H be a subgroup of PSL₂(F), and P a nontrivial Sylow p-subgroup of H whose normalizer properly contains P. Then H is an elementary-abelian-by-cyclic semidirect product with the stated order divisibilities, an A₅ group in the restricted characteristic case, a PGL₂ subfield group with 2m dividing f, or a PSL₂ subfield group with m dividing f. This is the plain public Huppert II.8.26 endpoint; every order, exponent and divisibility restriction is explicit in the formal statement.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean; declaration Glauberman.Dickson.huppert_II_8_26_dickson_case_p_part_normalizer_large. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Definitions.Def_cfsg_elementary_abelian
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Independence
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_26_dickson_case_p_part_normalizer_large
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (P : Sylow p H) (hP_nontrivial : Nat.card P ≠ 1)
    (hnormalizer : Subgroup.normalizer (P : Set H) ≠ (P : Subgroup H)) :
    (∃ m t : ℕ,
      t ∣ p ^ m - 1 ∧
      t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
      ∃ N C : Subgroup H,
        N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
        IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
    (∃ m : ℕ, p ^ m = 3 ∧
      (p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
      Nonempty (H ≃* alternatingGroup (Fin 5))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
      Nonempty (H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) := by sorry
