-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_isaacs_lem_5_28
-- name    : OddOrder.Isaacs.Ch05.isaacs_lem_5_28
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:08.827678+00:00
-- url     : https://prove2.me/theorems/9d46380c-8028-461c-80e3-184b33d5e52f
-- title:
--   Isaacs Lemma 5.28: Sylow conjugation centralizing the intersection when all $N_G(X)/C_G(X)$ are $p$-groups
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Suppose that for every $p$-subgroup $X\le G$, the quotient $N_G(X)/C_G(X)$ is a $p$-group. Then for any two Sylow $p$-subgroups $P,Q$ of $G$ there exists $c\in C_G(P\cap Q)$ with
--   $$cQc^{-1}=P.$$
--
--   This is the key lemma for Frobenius' normal $p$-complement theorem (Isaacs 5.26). The proof is by strong induction on the order of $D=P\cap Q$, choosing a counterexample with $|D|$ maximal.
--
--   **Formalization Note** The conclusion is written `c • Q = P` for the conjugation action of $G$ on Sylow subgroups; the hypothesis uses the quotient of the subgroup `normalizer X` by `(centralizer X).subgroupOf (normalizer X)`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Main.lean#L662-L952

import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

theorem isaacs_lem_5_28 [Finite G] {p : ℕ} [Fact p.Prime]
    (hH : ∀ X : Subgroup G, IsPGroup p X →
      IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
        (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))))
    (P Q : Sylow p G) :
    ∃ c ∈ Subgroup.centralizer (((P : Subgroup G) ⊓ (Q : Subgroup G)) : Set G),
      c • Q = P := by sorry

end

end OddOrder.Isaacs.Ch05
