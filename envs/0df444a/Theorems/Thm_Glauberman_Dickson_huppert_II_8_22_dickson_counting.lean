-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_dickson_counting
-- name    : Glauberman.Dickson.huppert_II_8_22_dickson_counting
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T12:41:14.317837+00:00
-- url     : https://prove2.me/theorems/a67310b2-1a1f-4c55-b669-16d1398e5ab1
-- title:
--   Dickson’s counting equation and normalizer data for PSL₂ subgroups
-- statement:
--   Let F have cardinality p^f with p prime, H ≤ PSL₂(F), and P a Sylow p-subgroup of H of order p^m. There is a finite conjugacy-representative family Z_i of nontrivial maximal cyclic subgroups of order prime to p, with normalizer multipliers s_i in {1,2}. Their orders divide one of the split or nonsplit torus orders. Multiplier 2 gives a dihedral normalizer. The Sylow normalizer has the stated p^m or p^m|Z_i| form when P is nontrivial, and the subgroup order satisfies Huppert II.8.22’s exact partition-counting equation. All representative, normalizer and arithmetic conditions are included in the formal conclusion.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean; declaration Glauberman.Dickson.huppert_II_8_22_dickson_counting. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
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

theorem Glauberman.Dickson.huppert_II_8_22_dickson_counting
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) :
    ∃ (r : ℕ) (Z : Fin r → Subgroup H) (s : Fin r → ℕ),
      (∀ i, IsCyclic (Z i)) ∧
      (∀ i, 1 < Nat.card (Z i)) ∧
      (∀ i, Nat.Coprime p (Nat.card (Z i))) ∧
      (∀ i (W : Subgroup H), IsCyclic W → Z i ≤ W → W = Z i) ∧
      (∀ W : Subgroup H, IsCyclic W → 1 < Nat.card W →
        Nat.Coprime p (Nat.card W) →
        (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
        ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom) ∧
      (∀ i j g,
        (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) ∧
      (∀ i, 0 < s i ∧ s i ≤ 2) ∧
      (∀ i,
        Nat.card (Subgroup.normalizer (Z i : Set H)) = Nat.card (Z i) * s i) ∧
      (∀ i, s i = 2 →
        Nonempty (Subgroup.normalizer (Z i : Set H) ≃*
          DihedralGroup (Nat.card (Z i)))) ∧
      (1 < p ^ m →
        (Nat.card (Subgroup.normalizer (P : Set H)) = p ^ m ∨
          ∃ i, Nat.card (Subgroup.normalizer (P : Set H)) =
            p ^ m * Nat.card (Z i))) ∧
      (∀ i,
        (Nat.card (Z i) ∣
            (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (Nat.card (Z i) ∣
            (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H =
        1 + ((p ^ m - 1) * Nat.card H) /
            Nat.card (Subgroup.normalizer (P : Set H)) +
          ∑ i, ((Nat.card (Z i) - 1) * Nat.card H) /
            (Nat.card (Z i) * s i) := by sorry
