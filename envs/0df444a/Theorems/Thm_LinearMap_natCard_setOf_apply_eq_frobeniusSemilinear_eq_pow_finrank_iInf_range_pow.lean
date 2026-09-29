-- Prove2me | Theorems.Thm_LinearMap_natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow
-- name    : LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3c054a93-fdbd-579a-af6c-91749dc5b346
-- title:
--   Semilinear Fitting count: #{Uv=Sv}=p^{dim W}
-- statement:
--   Let $k$ be an algebraically closed field, $p$ a prime with $\operatorname{char} k = p$, and $V$ a finite-dimensional $k$-vector space. Let $S \colon V \to V$ be an additive map which is Frobenius-semilinear in the sense that $S(c \cdot v) = c^{p} \cdot S(v)$ for all $c \in k$ and $v \in V$, and assume $S$ is bijective. Let $U \colon V \to V$ be $k$-linear and assume $U$ commutes with $S$, i.e. $U(S v) = S(U v)$ for every $v \in V$. The conclusion is an equality of natural numbers: the cardinality of the set $\{v \in V : U v = S v\}$ (as the `Nat.card` of the corresponding subtype) equals $p^{\,d}$, where $d$ is the $k$-dimension of the submodule $\bigsqcap_{n \in \mathbb{N}} \operatorname{range}(U^{n})$, the infimum over all natural numbers $n$ of the images $U^{n}(V)$, that is, the stable range of $U$. Since the right-hand side is nonzero, the statement in particular asserts that the set of such $v$ is finite; no separate finiteness hypothesis is imposed on $V$ beyond finite-dimensionality over $k$.
--
--   This is a semilinear Fitting-type count: the solutions of $Uv = Sv$ are the fixed vectors of the $p^{-1}$-semilinear additive bijection $S^{-1} \circ U$, an $\mathbf{F}_p$-subspace concentrated on the part of $V$ where $U$ is invertible, and their number is governed by the Lang–Steinberg surjectivity phenomenon in characteristic $p$. It is used in the count of torsion points on a modular curve via the characteristic polynomial of a Hecke operator, in [`ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne`](thm.html#ModularCurve.natCard_torsion_jOneC_eq_pow_natDegree_sub_natTrailingDegree_of_map_eq_charpoly_heckeTLinOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.natCard_setOf_apply_eq_frobeniusSemilinear_eq_pow_finrank_iInf_range_pow
    {k V : Type*} [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (S : V →+ V) (hS : ∀ (c : k) (v : V), S (c • v) = c ^ p • S v)
    (hSbij : Function.Bijective S)
    (U : V →ₗ[k] V) (hcomm : ∀ v : V, U (S v) = S (U v)) :
    Nat.card {v : V // U v = S v} =
      p ^ Module.finrank k ↥(⨅ n : ℕ, LinearMap.range (U ^ n)) := by sorry
