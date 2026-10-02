-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_partition_count_of_unique_family
-- name    : Glauberman.Dickson.huppert_II_8_22_partition_count_of_unique_family
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T12:24:12.619806+00:00
-- url     : https://prove2.me/theorems/61c7776e-8703-4347-bf68-66c2481caa69
-- title:
--   Counting a finite group partitioned by Sylow and cyclic conjugacy families
-- statement:
--   Let H be a finite group, p a prime, and P a Sylow p-subgroup of cardinality p^m. Let Z be a finite indexed family of subgroups. Suppose each nonidentity element belongs to exactly one indexed subgroup in the disjoint family consisting of all Sylow p-subgroups and all conjugates of the Z_i. Then |H| equals 1 plus (p^m-1)[H:N_H(P)] plus the sum of (|Z_i|-1)[H:N_H(Z_i)]. The uniqueness hypothesis includes the indexing, so no conjugacy family is counted twice.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean; declaration Glauberman.Dickson.huppert_II_8_22_partition_count_of_unique_family. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_22_partition_count_of_unique_family
    {H : Type*} [Group H] [Finite H] {p m r : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m)
    (Z : Fin r → Subgroup H)
    (hunique : ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H)) :
    Nat.card H =
      1 + (p ^ m - 1) *
          (Subgroup.normalizer (P : Set H)).index +
        ∑ i, (Nat.card (Z i) - 1) *
          (Subgroup.normalizer (Z i : Set H)).index := by sorry
