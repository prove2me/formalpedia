-- Prove2me | Theorems.Thm_OddOrder_GroupTheory_IsTISubset_sum_conjClassSet
-- name    : OddOrder.GroupTheory.IsTISubset.sum_conjClassSet
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:48.551791+00:00
-- url     : https://prove2.me/theorems/cefd9ed7-4fdf-414f-b564-ebfd772fbe61
-- title:
--   Conjugation-invariant sums over the saturation of a TI-subset
-- statement:
--   Let $G$ be a finite group, $L\le G$ a subgroup, and $A\subseteq G$ a TI-subset with normalizer bound $L$, meaning: whenever $g\in G$ and some $a\in A$ has $gag^{-1}\in A$, then $g\in L$. Assume $A$ is stabilized by $L$ ($lAl^{-1}=A$ for all $l\in L$). Let $f:G\to M$ be a function into an additive commutative monoid $M$ that is conjugation invariant: $f(gxg^{-1})=f(x)$ for all $g,x\in G$. Then the sum of $f$ over the saturation $A^G=\{gag^{-1}\}$ equals $[G:L]$ times the sum over $A$:
--   $$\sum_{x\in A^G}f(x)=[G:L]\cdot\sum_{a\in A}f(a).$$
--
--   The saturation is the disjoint union of the conjugates $gA$ indexed by cosets $gL$ (disjointness is the TI condition), and each conjugate contributes the same sum. This is the weighted refinement of the cardinality count of the saturation, and the Parseval-split engine for the norm estimates of Peterfalvi (13.10).
--
--   **Formalization Note** `IsTISubset A L` is the project definition of the TI condition; the saturation is `conjClassSet A`; the factor $[G:L]$ acts by `L.index • _` (repeated addition in $M$).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/TISubsetCounting.lean#L50-L144

import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

namespace IsTISubset

open scoped Pointwise

theorem sum_conjClassSet [Finite G] {A : Set G} {L : Subgroup G}
    {M : Type*} [AddCommMonoid M] (f : G → M)
    (hTI : IsTISubset A L) (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) :
    ∑ x ∈ (Set.toFinite (conjClassSet A)).toFinset, f x
      = L.index • ∑ a ∈ (Set.toFinite A).toFinset, f a := by sorry

end IsTISubset

end OddOrder.GroupTheory
