-- Prove2me | Theorems.Thm_Glauberman_Dickson_h824_alternating_five_of_cyclic_family
-- name    : Glauberman.Dickson.h824_alternating_five_of_cyclic_family
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T12:57:55.953099+00:00
-- url     : https://prove2.me/theorems/4118aea6-0b8e-422f-ae93-617ef700b918
-- title:
--   Dickson cyclic-family recognition of A₅
-- statement:
--   Let F be a finite field of cardinality p^f, and H ≤ PSL₂(F). Assume H has order 60 and a trivial Sylow p-subgroup. Let three pairwise nonconjugate representatives cover its maximal nontrivial cyclic subgroups of order prime to p. Suppose their orders, in a specified ordering, are 5, 3, 2, and their normalizer indices are 6, 10, 15; the formal statement also retains the multiplier-two normalizer data from Dickson’s counting setup. Then H is isomorphic to A₅. This isolates the corresponding exceptional-group recognition step within the upstream proof of Huppert II.8.24.
-- source:
--   Original formalization: Qiuzhen-CFSG/CFSG, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, Apache-2.0. Original authorship belongs to the upstream contributors. Source: https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean . arexychen lifted the existing local recognition stage into an explicit theorem, extracted dependencies, replayed it in the pinned environment and validated the proof. No new classification assumption is introduced.

import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.CharP.CharAndCard
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
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
set_option autoImplicit false
universe u v
open scoped Pointwise

theorem Glauberman.Dickson.h824_alternating_five_of_cyclic_family
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))
    (Z : Fin 3 → Subgroup H)
    (hcyclic : ∀ i, IsCyclic (Z i))
    (hnontrivial : ∀ i, 1 < Nat.card (Z i))
    (hcoprime : ∀ i, Nat.Coprime p (Nat.card (Z i)))
    (hmaximal : ∀ i (W : Subgroup H),
      IsCyclic W → Z i ≤ W → W = Z i)
    (hrepresentative : ∀ W : Subgroup H,
      IsCyclic W → 1 < Nat.card W →
      Nat.Coprime p (Nat.card W) →
      (∀ V : Subgroup H, IsCyclic V → W ≤ V → V = W) →
      ∃ i g, W = (Z i).map (MulAut.conj g).toMonoidHom)
    (hdistinct : ∀ i j g,
      (Z i).map (MulAut.conj g).toMonoidHom = Z j → i = j)
    (P : Sylow p H) (hPcard : Nat.card P = p ^ 0)
    (s : Fin 3 → ℕ)
    (hnormalizerZ : ∀ a, Nat.card (Subgroup.normalizer (Z a : Set H)) = Nat.card (Z a) * s a)
    (hs_all_two : ∀ a, s a = 2)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi_five : Nat.card (Z i) = 5) (hzj_three : Nat.card (Z j) = 3)
    (hzk_two : Nat.card (Z k) = 2)
    (hindices_five :
      (Subgroup.normalizer (Z i : Set H)).index = 6 ∧
      (Subgroup.normalizer (Z j : Set H)).index = 10 ∧
      (Subgroup.normalizer (Z k : Set H)).index = 15)
    (hHcard60 : Nat.card H = 60) :
    Nonempty (H ≃* alternatingGroup (Fin 5)) := by sorry
