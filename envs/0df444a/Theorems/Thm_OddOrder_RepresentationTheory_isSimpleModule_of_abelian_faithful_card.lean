-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_isSimpleModule_of_abelian_faithful_card
-- name    : OddOrder.RepresentationTheory.isSimpleModule_of_abelian_faithful_card
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:44:46.536562+00:00
-- url     : https://prove2.me/theorems/96278b9a-69bb-4d03-a903-f7ad800ef2da
-- title:
--   Singer irreducibility for a faithful abelian action of order $(p^q-1)/(p-1)$
-- statement:
--   Let $p,q$ be primes with $q$ odd. Let $C$ be a finite commutative group and $M$ a finite additive commutative group which is a module over the group algebra $\mathbb{F}_p[C]$ (that is, $C$ acts $\mathbb{F}_p$-linearly), with $p\nmid|C|$ (that is, $|C|\ne0$ in $\mathbb{Z}/p$). Suppose $|M|=p^q$, $|C|=\dfrac{p^q-1}{p-1}$, and the action is faithful (the only $c\in C$ acting as the identity on $M$ is $c=1$). Then $M$ is a simple $\mathbb{F}_p[C]$-module (irreducible), without assuming that $C$ is cyclic.
--
--   This allows one to deduce that $C$ is cyclic (via the Singer embedding) rather than assuming it, as in Peterfalvi (13.2.a). The proof takes a primitive prime divisor $r$ of $p^q-1$ dividing $|C|$ and applies a fixed-point argument showing $q\mid(q-1)!$, contradicting Wilson's theorem.
--
--   **Formalization Note** The module structure is `Module (MonoidAlgebra (ZMod p) C) M`, irreducibility is `IsSimpleModule`, and the order of $M$ is `Nat.card M`. The source section carries `[IsCyclic C]` as a variable, but it is omitted from this statement, so $C$ is not assumed cyclic.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SingerField.lean#L290-L403

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

omit [IsCyclic C] in

theorem isSimpleModule_of_abelian_faithful_card {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    [NeZero (Nat.card C : ZMod p)]
    (hcardM : Nat.card M = p ^ q)
    (hcardC : Nat.card C = (p ^ q - 1) / (p - 1))
    (hfaith : ∀ c : C, (∀ x : M, MonoidAlgebra.of (ZMod p) C c • x = x) → c = 1) :
    IsSimpleModule (MonoidAlgebra (ZMod p) C) M := by sorry

end Irreducibility

end OddOrder.RepresentationTheory
