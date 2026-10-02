-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_5_a_psl2_partition
-- name    : Glauberman.Dickson.huppert_II_8_5_a_psl2_partition
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T12:01:51.47682+00:00
-- url     : https://prove2.me/theorems/60cff21b-22ea-4683-809c-4d2d61b082e4
-- title:
--   The Sylow and torus partition of PSL₂ over a finite field
-- statement:
--   Let F have cardinality p^f with p prime and let P be a Sylow p-subgroup of PSL₂(F). There are cyclic subgroups U and S of respective orders (|F|-1)/d and (|F|+1)/d, where d=gcd(|F|-1,2), such that every nonidentity element lies in a unique subgroup among the conjugates of P, U and S. This is Huppert II.8.5(a), stated as uniqueness of the containing subgroup.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonPSL2Partition.lean; declaration Glauberman.Dickson.huppert_II_8_5_a_psl2_partition. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_5_a_psl2_partition
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f)
    (P : Sylow p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    ∃ U S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
      IsCyclic U ∧
      Nat.card U =
        (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      IsCyclic S ∧
      Nat.card S =
        (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2 ∧
      ∀ x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F, x ≠ 1 →
        ∃! T : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F),
          x ∈ T ∧
            ((∃ g, T = (P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)).map
              (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
            (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by sorry
