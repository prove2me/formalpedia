-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
-- name    : GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/6239db5c-8958-5f78-8956-8d0129273161
-- title:
--   Irreducible components through a rational point of a group scheme
-- statement:
--   Let $k$ be an algebraically closed field, let $N$ be a scheme and let $gN : N \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Suppose $gN$ carries a relative group law `RelativeGroupLaw`, that is: for every $k$-scheme $t : T \to \operatorname{Spec} k$ the set of $T$-points over $t$ — pairs consisting of a morphism $T \to N$ whose composite with $gN$ equals $t$ — is equipped with a multiplication, a distinguished element and an inversion satisfying associativity, the two unit laws and the left inverse law, the multiplication being natural in the sense that for $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition with $\psi$ carries the product of two $T$-points over $t$ to the product of their precompositions. Let $x$ be a point over the identity of $\operatorname{Spec} k$, i.e. a morphism $\operatorname{Spec} k \to N$ whose composite with $gN$ is the identity, so a $k$-rational point of $N$, and write $\bar x$ for the image under the underlying continuous map of $x$ of the closed point of $\operatorname{Spec} k$. Then any two irreducible components $Z$, $Z'$ of the topological space of $N$ with $\bar x \in Z$ and $\bar x \in Z'$ are equal.
--
--   This is the standard fact that a group scheme locally of finite type over a field has pairwise disjoint irreducible components, in the form needed to speak of the irreducible component of a given rational point; over an algebraically closed field every closed point is rational, so each point of $N$ lies on a unique component. It is used in the construction of the identity component of such a group scheme, namely in the statements producing an open immersion with irreducible source whose range is the connected component and a closed immersion into an abelian-scheme property bundle of finite index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.eq_of_mem_irreducibleComponents_of_apply_closedPoint_mem
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}} {gN : N ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType gN] (LN : RelativeGroupLaw k gN)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) gN)
    {Z Z' : Set N} (hZ : Z ∈ irreducibleComponents N) (hZ' : Z' ∈ irreducibleComponents N)
    (hx : x.1 (IsLocalRing.closedPoint k) ∈ Z) (hx' : x.1 (IsLocalRing.closedPoint k) ∈ Z') :
    Z = Z' := by sorry
