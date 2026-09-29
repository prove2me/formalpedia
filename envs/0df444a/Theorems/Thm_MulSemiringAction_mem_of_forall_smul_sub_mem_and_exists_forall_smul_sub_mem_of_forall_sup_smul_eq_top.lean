-- Prove2me | Theorems.Thm_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
-- name    : MulSemiringAction.mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/e9172f2a-94ad-58c2-b2b5-9fe42536d795
-- title:
--   Element-wise orbit Chinese remainder for comaximal translates of P
-- statement:
--   Let $B$ be a commutative ring carrying an action of a finite group $G$ by ring automorphisms, and let $I$ and $P$ be ideals of $B$ with $I \le P$. Assume: $I$ is stable under the action, in the sense that $g \cdot b \in I$ whenever $b \in I$; for every $g \in G$ with $g \cdot P \ne P$ one has $P \sqcup g \cdot P = \top$, i.e. $P$ and its translate are comaximal; and every $b \in B$ with $g \cdot b \in P$ for all $g \in G$ lies in $I$ (so the intersection of the translates of $P$ is contained in $I$). The conclusion is the conjunction of two element-wise statements. First, if $b \in B$ satisfies $g \cdot b - b \in I$ for all $g \in G$ and $b \in P$, then $b \in I$. Second, for every $s \in B$ such that $g \cdot s - s \in P$ for all $g$ in the stabiliser of $P$ (those $g$ with $g \cdot P = P$), there exists $r \in B$ with $g \cdot r - r \in I$ for all $g \in G$ and $r - s \in P$. Together these express injectivity and surjectivity of the map $(B/I)^{G} \to (B/P)^{\mathrm{Stab}(P)}$ induced by reduction, without quotients being formed.
--
--   This is the element-wise form of the Chinese remainder decomposition of $B/I$ along the $G$-orbit of $P$, whose $G$-invariants reduce to the invariants of $B/P$ under the stabiliser (decomposition group) of $P$; the two clauses are exactly injectivity and surjectivity of reduction on invariants. It is used in the construction of charts for modular curves with full level structure, where the special fibre splits along the components above the uniformiser and the level structure must be descended to the invariant subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem MulSemiringAction.mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top
    {B : Type*} [CommRing B] {G : Type*} [Group G] [Finite G] [MulSemiringAction G B]
    (I P : Ideal B) (hIP : I ≤ P) (hI : ∀ (g : G) (b : B), b ∈ I → g • b ∈ I)
    (hmax : ∀ g : G, g • P ≠ P → P ⊔ g • P = ⊤)
    (hinf : ∀ b : B, (∀ g : G, g • b ∈ P) → b ∈ I) :
    (∀ b : B, (∀ g : G, g • b - b ∈ I) → b ∈ P → b ∈ I) ∧
    (∀ s : B, (∀ g : G, g • P = P → g • s - s ∈ P) →
      ∃ r : B, (∀ g : G, g • r - r ∈ I) ∧ r - s ∈ P) := by sorry
