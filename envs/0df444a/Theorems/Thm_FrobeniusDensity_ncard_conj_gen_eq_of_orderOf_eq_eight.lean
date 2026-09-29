-- Prove2me | Theorems.Thm_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight
-- name    : FrobeniusDensity.ncard_conj_gen_eq_of_orderOf_eq_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/5d8119fa-64a7-5de6-96fd-567c82a787e8
-- title:
--   Class count for an order-8 element conjugate to its cube
-- statement:
--   Let $G$ be a finite group, and let $\sigma,\tau \in G$ be such that $\sigma$ has order $8$ and $\sigma$ is conjugate in $G$ to $\sigma^{3}$. Consider the set of those $g \in G$ for which there exists a natural number $k$ coprime to $\operatorname{ord}(\sigma) = 8$ with $g\,\sigma^{k}\,g^{-1} = \tau$; since $\sigma^{k}$ depends only on $k$ modulo $8$, this is the set of $g$ conjugating some odd power of $\sigma$ to $\tau$. The assertion is that the cardinality of this set (as a set in $G$, measured by `Set.ncard`) equals $2\,|C_G(\sigma)|\,\bigl(\mathbf 1[\sigma \sim \tau] + \mathbf 1[\sigma^{5} \sim \tau]\bigr)$, where $C_G(\sigma)$ is the centraliser in $G$ of the singleton set $\{\sigma\}$, its order is taken as `Nat.card`, and the two indicator terms are $1$ or $0$ according as $\tau$ is conjugate to $\sigma$, respectively to $\sigma^{5}$, in $G$. In particular the count is $0$ unless $\tau$ lies in the conjugacy class of $\sigma$ or of $\sigma^{5}$, and it is $2\,|C_G(\sigma)|$ when exactly one of these holds.
--
--   This is the weight attached to the rational class of an order-$8$ element in the Frobenius-type density computation: the four odd exponents $1,3,5,7$ fall, under the hypothesis $\sigma \sim \sigma^{3}$ (whence $\sigma^{7} \sim \sigma^{5}$), into the two classes of $\sigma$ and $\sigma^{5}$, each contributing two cosets of the centraliser. It is used in the Langlands–Tunnell part of the development, in the additivity of the tower Dirichlet density for order-$8$ elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight.lean

import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Set.Card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical in

theorem FrobeniusDensity.ncard_conj_gen_eq_of_orderOf_eq_eight {G : Type*} [Group G] [Finite G]
    (σ τ : G) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = 2 * Nat.card (Subgroup.centralizer ({σ} : Set G)) *
          ((if IsConj σ τ then 1 else 0) + (if IsConj (σ ^ 5) τ then 1 else 0)) := by sorry
