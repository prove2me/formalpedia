-- Prove2me | Theorems.Thm_OddOrder_GroupTheory_IsTISubset_induce_apply_of_mem_conj
-- name    : OddOrder.GroupTheory.IsTISubset.induce_apply_of_mem_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:42.35519+00:00
-- url     : https://prove2.me/theorems/3cfe452b-2843-4990-8c47-a60cd8de8f02
-- title:
--   Induced class function on the saturation of a TI-subset
-- statement:
--   Let $G$ be a finite group, $k$ a field, $L\le G$ a subgroup with $|L|$ invertible in $k$, and $A\subseteq L$ a TI-subset with normalizer bound $L$ (if $gag^{-1}\in A$ for some $a\in A$ then $g\in L$) that is stabilized by $L$. Let $\alpha$ be a class function of $L$ with values in $k$ that is supported on $A$ ($\alpha(w)=0$ for $w\in L$ with $w\notin A$). Then for $a\in A$ and $g=yay^{-1}$ with $y\in G$, the induced class function takes the value
--   $$\mathrm{Ind}_L^G\alpha\,(g)=\alpha(a).$$
--
--   The nonvanishing induction summands are indexed exactly by the coset $yL$, each contributing $\alpha(a)$, and the normalization $1/|L|$ collapses the count. This identifies the TI Dade isometry with $\mathrm{Ind}_L^G$, as in Peterfalvi (7.2)/(13.2.e).
--
--   **Formalization Note** `IsTISubset` is the project definition of the TI condition; class functions are `ClassFunction ↥L k` and induction is `ClassFunction.induce L`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/TISubsetCounting.lean#L146-L219

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

theorem induce_apply_of_mem_conj {k : Type*} [Field k] [Fintype G]
    {A : Set G} {L : Subgroup G} [Invertible (Nat.card ↥L : k)]
    (hTI : IsTISubset A L) (hAL : A ⊆ (L : Set G))
    (hstab : ∀ l ∈ L, MulAut.conj l • A = A)
    (α : OddOrder.RepresentationTheory.ClassFunction ↥L k)
    (hsupp : ∀ w : ↥L, (w : G) ∉ A → α w = 0)
    {a g y : G} (ha : a ∈ A) (hg : g = y * a * y⁻¹) :
    OddOrder.RepresentationTheory.ClassFunction.induce L α g = α ⟨a, hAL ha⟩ := by sorry

end IsTISubset

end OddOrder.GroupTheory
