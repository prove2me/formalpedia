-- Prove2me | Theorems.Thm_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer
-- name    : FrobeniusDensity.card_setOf_isConj_mul_card_centralizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/02b51d58-d505-5d74-915d-eb33470d08f4
-- title:
--   Conjugacy class size times centralizer order equals |G|
-- statement:
--   Let $G$ be a group (no finiteness is assumed) and let $\sigma \in G$. The theorem asserts the identity $$\#\{\tau \in G : \mathrm{IsConj}\,\sigma\,\tau\} \cdot \#C_G(\sigma) = \#G,$$ where the first factor is the cardinality of the set of those $\tau \in G$ that are conjugate to $\sigma$ (i.e. $\tau = c\sigma c^{-1}$ for some $c \in G$), the second factor is the cardinality of the subgroup `Subgroup.centralizer` of the singleton $\{\sigma\}$, that is of the centralizer $C_G(\sigma) = \{g \in G : g\sigma = \sigma g\}$, and the right-hand side is the cardinality of $G$. All three cardinalities are natural numbers in the sense of `Nat.card`, so each is $0$ when the corresponding type is infinite; in particular the statement is an identity of natural numbers valid for arbitrary $G$, and for infinite $G$ it records that the conjugacy class is infinite or the centralizer has infinite order.
--
--   This is the orbit–stabiliser theorem for the conjugation action of $G$ on itself, equivalently the assertion that the size of a conjugacy class is the index of the centralizer (the summand form of the class equation). It is used in the Frobenius density computations, where the density attached to a conjugacy class carries the weight $\#[\sigma]/\#G = 1/\#C_G(\sigma)$, and is cited by [`LanglandsTunnell.towerDirichletDensity_add_of_orderOf_eq_eight`](thm.html#LanglandsTunnell.towerDirichletDensity_add_of_orderOf_eq_eight).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.lean

import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.card_setOf_isConj_mul_card_centralizer {G : Type*} [Group G] (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by sorry
