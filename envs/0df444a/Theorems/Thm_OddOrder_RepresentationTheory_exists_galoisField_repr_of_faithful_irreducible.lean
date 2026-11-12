-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_exists_galoisField_repr_of_faithful_irreducible
-- name    : OddOrder.RepresentationTheory.exists_galoisField_repr_of_faithful_irreducible
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:48.111258+00:00
-- url     : https://prove2.me/theorems/85b862c0-f743-4b96-a58f-5322930d7702
-- title:
--   Galois-field realization of a faithful irreducible abelian action
-- statement:
--   Let $p$ be a prime, $q\ne0$ a natural number, $C$ a commutative group and $M$ a finite additive commutative group carrying the structure of an $\mathbb{F}_p[C]$-module that is simple (irreducible). Suppose $|M|=p^q$ and the action of $C$ is faithful (the only $c\in C$ acting as the identity on $M$ is $c=1$). Then there are an additive isomorphism $e:M\to\mathbb{F}_{p^q}$ and an injective homomorphism $\mu:C\to\mathbb{F}_{p^q}^{\times}$ such that
--   $$e(c\cdot x)=\mu(c)\,e(x)\qquad(c\in C,\ x\in M).$$
--
--   That is, $M$ is additively $\mathbb{F}_{p^q}$ and $C$ acts by multiplication through $\mu$. No order condition on $C$ is imposed, and irreducibility is taken as a hypothesis. This is the branch-independent Singer entry used in Peterfalvi (9.7.b), including the divided-order branch needed in (14.6).
--
--   **Formalization Note** The module structure is `Module (MonoidAlgebra (ZMod p) C) M`, irreducibility is the instance `IsSimpleModule`; `[IsCyclic C]` and `[Finite C]` from the ambient section are omitted, so $C$ need not be cyclic or finite.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SingerField.lean#L405-L455

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RepresentationTheory.Maschke
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.GeomSum

namespace OddOrder.RepresentationTheory

universe u

variable {p : ℕ} {C M : Type u} [CommGroup C] [AddCommGroup M]
  [Module (MonoidAlgebra (ZMod p) C) M]

section Irreducibility

variable {p : ℕ} [Fact p.Prime] {C M : Type u}
  [CommGroup C] [IsCyclic C] [Finite C]
  [AddCommGroup M] [Module (MonoidAlgebra (ZMod p) C) M] [Finite M]

omit [IsCyclic C] [Finite C] in

theorem exists_galoisField_repr_of_faithful_irreducible {q : ℕ} (hq : q ≠ 0)
    [IsSimpleModule (MonoidAlgebra (ZMod p) C) M]
    (hcardM : Nat.card M = p ^ q)
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    ∃ (e : M ≃+ GaloisField p q) (μ : C →* (GaloisField p q)ˣ),
      Function.Injective μ ∧
      ∀ (c : C) (x : M),
        e (MonoidAlgebra.of (ZMod p) C c • x) = (μ c : GaloisField p q) * e x := by sorry

end Irreducibility

end OddOrder.RepresentationTheory
