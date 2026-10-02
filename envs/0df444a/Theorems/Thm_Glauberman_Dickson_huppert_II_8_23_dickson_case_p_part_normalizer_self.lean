-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_23_dickson_case_p_part_normalizer_self
-- name    : Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T13:22:10.006528+00:00
-- url     : https://prove2.me/theorems/1b0d6d5a-e5a9-46f7-adb4-413352f10053
-- title:
--   Dickson’s branch with a nontrivial self-normalizing Sylow subgroup
-- statement:
--   Let F have cardinality p^f with p prime, H ≤ PSL₂(F), and P a nontrivial Sylow p-subgroup of H of order p^m. If P is its own normalizer in H, then H is elementary abelian of order p^m, or p^m=2 and H is a dihedral group of order 2z with z odd and dividing a split or nonsplit torus order, or p^m=3 and H is isomorphic to A₄. The definition of elementary abelian explicitly requires commutativity and exponent dividing p.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCase823.lean; declaration Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Definitions.Def_cfsg_elementary_abelian
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
    {F : Type u} [Field F] [Finite F] {p f m : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (P : Sylow p H) (hPcard : Nat.card P = p ^ m) (hpm : 1 < p ^ m)
    (hnormalizer : Subgroup.normalizer (P : Set H) = (P : Subgroup H)) :
    (Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∨
    (p ^ m = 2 ∧ ∃ z : ℕ, ¬ 2 ∣ z ∧
      ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
        (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
      Nat.card H = 2 * z ∧ Nonempty (H ≃* DihedralGroup z)) ∨
    (p ^ m = 3 ∧ Nonempty (H ≃* alternatingGroup (Fin 4))) := by sorry
