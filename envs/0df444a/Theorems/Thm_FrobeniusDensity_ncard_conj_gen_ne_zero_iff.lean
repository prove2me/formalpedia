-- Prove2me | Theorems.Thm_FrobeniusDensity_ncard_conj_gen_ne_zero_iff
-- name    : FrobeniusDensity.ncard_conj_gen_ne_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/e9b8d8d3-102e-5848-801b-c69447de9bd1
-- title:
--   Nonzero conjugating count iff some power of σ is conjugate to τ
-- statement:
--   Let $G$ be a finite group and let $\sigma, \tau \in G$. Consider the set of those $g \in G$ for which there exists a natural number $k$ coprime to the order of $\sigma$ with $g \sigma^k g^{-1} = \tau$; here `Nat.Coprime` is the condition that $\gcd(k, \mathrm{ord}(\sigma)) = 1$, and the cardinality used is `Set.ncard`, the natural-number cardinality of a set (zero for infinite sets, but the ambient group is finite, so the set is finite). The assertion is that this cardinality is nonzero if and only if there exists a natural number $k$ coprime to $\mathrm{ord}(\sigma)$ such that $\sigma^k$ is conjugate to $\tau$ in $G$, i.e. `IsConj (σ ^ k) τ` holds. In other words, the counting set is nonempty exactly when some power $\sigma^k$ with $k$ coprime to the order of $\sigma$ — equivalently, some generator of the cyclic group $\langle \sigma \rangle$ — lies in the conjugacy class of $\tau$.
--
--   This is the elementary bridge between a cardinality statement and an existence statement: it converts the nonvanishing of the number of conjugating elements into the assertion that $\tau$ is conjugate to a generator of $\langle\sigma\rangle$. It is used in the derivation of the statement of Frobenius's density theorem from an asymptotic count of degree-one primes, in [`FrobeniusDensity.statement_of_degOneAsymptotic`](thm.html#FrobeniusDensity.statement_of_degOneAsymptotic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FrobeniusDensity_ncard_conj_gen_ne_zero_iff.lean

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Set.Card

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FrobeniusDensity.ncard_conj_gen_ne_zero_iff {G : Type*} [Group G] [Finite G]
    (σ τ : G) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard ≠ 0
      ↔ ∃ k : ℕ, k.Coprime (orderOf σ) ∧ IsConj (σ ^ k) τ := by sorry
