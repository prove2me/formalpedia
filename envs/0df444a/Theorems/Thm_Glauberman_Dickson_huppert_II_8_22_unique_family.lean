-- Prove2me | Theorems.Thm_Glauberman_Dickson_huppert_II_8_22_unique_family
-- name    : Glauberman.Dickson.huppert_II_8_22_unique_family
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T12:15:02.646892+00:00
-- url     : https://prove2.me/theorems/7851435d-057a-4605-ac8b-1415ee490e98
-- title:
--   Unique Sylow or maximal cyclic family for nonidentity subgroup elements in PSL₂
-- statement:
--   Let F have cardinality p^f with p prime and H be a subgroup of PSL₂(F). Choose pairwise nonconjugate representatives Z_i for the maximal nontrivial cyclic subgroups of H whose orders are prime to p. Then every nonidentity element of H lies in a unique indexed member of the family of Sylow p-subgroups of H and conjugates of the Z_i. The formal statement spells out cyclicity, nontriviality, prime-to-p orders, maximality, coverage and pairwise nonconjugacy of the representatives.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, original source authors, Apache-2.0; commit 96b2a02085dc678f3e0a97b334c31ada599c55fd; https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonCounting.lean; declaration Glauberman.Dickson.huppert_II_8_22_unique_family. arexychen contributes extraction, target-environment replay, theorem-DAG packaging and validation, not original authorship of Dickson classification.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Transfer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
universe u v
open scoped Pointwise Classical

theorem Glauberman.Dickson.huppert_II_8_22_unique_family
    {F : Type u} [Field F] [Finite F] {p f r : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (Z : Fin r → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (_hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j) :
    ∀ x : H, x ≠ 1 →
      ∃! A : (Sylow p H) ⊕
          (Σ i : Fin r, {W : Subgroup H // ∃ g : H,
            W = (Z i).map (MulAut.conj g).toMonoidHom}),
        x ∈ match A with
          | Sum.inl Q => (Q : Subgroup H)
          | Sum.inr z => (z.2.1 : Subgroup H) := by sorry
