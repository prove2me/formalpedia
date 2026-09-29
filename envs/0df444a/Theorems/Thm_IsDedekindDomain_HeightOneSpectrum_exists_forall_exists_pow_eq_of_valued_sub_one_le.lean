-- Prove2me | Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le
-- name    : IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/3465222f-a631-5032-81d8-19bfc8c09420
-- title:
--   Elements near 1 in Kᵥ are n-th powers
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $n$ be a natural number with $n>0$. The assertion is that there exists a natural number $m$ with the following property: for every element $a$ of the $v$-adic completion `v.adicCompletion K` of $K$ whose canonical valuation satisfies $\mathrm{v}(a-1) \le \exp(-m)$ — here the valuation takes values in $\mathbb{Z}^{\mathrm{mult}}$ with zero adjoined and $\exp$ is the multiplicative embedding of $\mathbb{Z}$, so that the condition says that $a-1$ lies in the $m$-th power of the maximal ideal — there exists $c$ in the same completion with $c^n = a$. Thus the $n$-th power map on $K_v$ hits every element of a sufficiently small neighbourhood $1 + \mathfrak{m}_v^m$ of $1$, with the bound $m$ depending only on $K$, $v$ and $n$, uniformly in $a$; no invertibility of $n$ in the residue characteristic is assumed.
--
--   This is the standard consequence of Hensel's lemma applied to $X^n - a$: the subgroup of $n$-th powers of $K_v^\times$ is open, since it contains a full congruence neighbourhood of $1$. It is used in the idelic class field theory part of the development, in [`M4aHerbrand.exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic`](thm.html#M4aHerbrand.exists_forall_mem_zpowers_idelicArtinMap_single_of_isCyclic), where one needs the local norm subgroups to be open so that global elements meet every class modulo norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_forall_exists_pow_eq_of_valued_sub_one_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_forall_exists_pow_eq_of_valued_sub_one_le
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∀ a : v.adicCompletion K,
      Valued.v (a - 1) ≤ WithZero.exp (-(m : ℤ)) → ∃ c : v.adicCompletion K, c ^ n = a := by sorry
