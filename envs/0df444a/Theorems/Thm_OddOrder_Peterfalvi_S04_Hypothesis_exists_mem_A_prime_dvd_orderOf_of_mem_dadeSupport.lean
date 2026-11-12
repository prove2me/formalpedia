-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S04_Hypothesis_exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport
-- name    : OddOrder.Peterfalvi.S04.Hypothesis.exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:13:36.251867+00:00
-- url     : https://prove2.me/theorems/3dda2528-7276-438b-a9c1-00ad96d95419
-- title:
--   Peterfalvi: elements of the Dade support carry a prime divisor of $o(a)$
-- statement:
--   Let $G$ be a finite group, $A\subseteq G$ a subset and $L\le G$ a subgroup, and let `hyp : Hypothesis G A L` be the Dade-isometry hypothesis package of Peterfalvi's Section 4 (`OddOrder.Peterfalvi.S04.Hypothesis`). Let $\tilde A$ denote its Dade support `hyp.dadeSupport`. If $x\in\tilde A$, then
--   $$\exists\, a\in A,\ \exists\, r\ \text{prime},\quad r\mid o(a)\ \text{ and }\ r\mid o(x).$$
--
--   The elements of $\tilde A$ are conjugates of products $a\cdot h$ with $a\in A$ and $h$ in a subgroup $H(a)$ centralizing $a$ and of coprime order; the statement is the order-theoretic input used to separate Dade supports in the analysis of the Peterfalvi (13.19)-type disjointness arguments.
--
--   **Formalization Note.** `[Fintype G]` is assumed; $o(\cdot)$ is `orderOf`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S04_DadeIsometryBasic.lean#L167-L209

import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_CoprimeConjugacy
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassFunction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeHypothesisCore
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometryBasic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

namespace OddOrder.Peterfalvi.S04

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

namespace Hypothesis

variable {A A₁ : Set G} {L : Subgroup G}

variable [Fintype G]

theorem exists_mem_A_prime_dvd_orderOf_of_mem_dadeSupport (hyp : Hypothesis G A L)
    {x : G} (hx : x ∈ hyp.dadeSupport) :
    ∃ a ∈ A, ∃ r : ℕ, r.Prime ∧ r ∣ orderOf a ∧ r ∣ orderOf x := by sorry

end Hypothesis

end OddOrder.Peterfalvi.S04
