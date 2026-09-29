-- Prove2me | Theorems.Thm_HopfOrder_counit_mem_range_sup
-- name    : HopfOrder.counit_mem_range_sup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/6ca3e1fe-87c2-5962-bb74-4e632f72ce65
-- title:
--   Counit integrality is preserved by joins of subalgebras
-- statement:
--   Let $R$ be a commutative ring, $K$ a field equipped with an $R$-algebra structure, and $A$ a commutative ring carrying a Hopf algebra structure over $K$ together with an $R$-algebra structure compatible with that of $K$ (a scalar tower $R \to K \to A$). Let $S$ and $S'$ be $R$-subalgebras of $A$. Assume that the $K$-linear counit $\varepsilon \colon A \to K$ of the coalgebra structure carries every element of $S$ into the range of the structure map $R \to K$, and likewise carries every element of $S'$ into that range. The conclusion is that the same holds for the join $S \sqcup S'$, the smallest $R$-subalgebra of $A$ containing both $S$ and $S'$: for every $x \in S \sqcup S'$, the element $\varepsilon(x)$ of $K$ lies in the image of $R \to K$. No finiteness, spanning or comultiplication hypotheses on $S$ or $S'$ are assumed; only the counit condition enters and only the counit condition is concluded.
--
--   This is the counit clause in the statement that the join of two Hopf orders of a $K$-Hopf algebra over a subring $R \subseteq K$ is again stable under the Hopf structure maps, the remaining clauses (module-finiteness, $K$-spanning, comultiplication and antipode stability) being handled separately. It is used in the construction of a greatest Hopf order, [`HopfOrder.exists_isGreatest`](thm.html#HopfOrder.exists_isGreatest), and in [`HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one`](thm.html#HopfAlgebra.existsUnique_bialgHom_baseChange_eq_of_pow_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfOrder_counit_mem_range_sup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

theorem HopfOrder.counit_mem_range_sup
    {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
    {A : Type w} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] {S S' : Subalgebra R A}
    (hS : ∀ x ∈ S, Coalgebra.counit (R := K) x ∈ (algebraMap R K).range)
    (hS' : ∀ x ∈ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range) :
    ∀ x ∈ S ⊔ S', Coalgebra.counit (R := K) x ∈ (algebraMap R K).range := by sorry
