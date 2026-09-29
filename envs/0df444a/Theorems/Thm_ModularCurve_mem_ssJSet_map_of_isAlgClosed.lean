-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
-- name    : ModularCurve.mem_ssJSet_map_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/1c2be3f8-6bd3-5d82-940c-351bad73cecd
-- title:
--   Supersingular j-invariants transfer along maps from algebraically closed fields
-- statement:
--   Let $q$ be a prime, and let $k_0$ and $k$ be fields of characteristic $q$ with $k_0$ algebraically closed. Let $\theta \colon k_0 \to k$ be a ring homomorphism and $a \in k_0$. Write $\mathrm{ssJSet}\,q\,K$ for the set of those $j \in K$ such that every Weierstrass curve $W$ over $K$ which is elliptic (nonvanishing discriminant) and has $j$-invariant $W.j = j$ has no nontrivial $q$-torsion in the group of affine points: every $P \in W(K)$ with $q \cdot P = 0$ equals $0$. The hypothesis is that $a \in \mathrm{ssJSet}\,q\,k_0$, i.e. every elliptic Weierstrass curve over $k_0$ with $j$-invariant $a$ has trivial $q$-torsion over $k_0$ itself. The conclusion is that $\theta(a) \in \mathrm{ssJSet}\,q\,k$: every elliptic Weierstrass curve over $k$ whose $j$-invariant equals $\theta(a)$ has no nonzero point killed by $q$ in its group of $k$-rational affine points. No separability, algebraic closedness or finiteness assumption is imposed on the target field $k$, and $\theta$ is an arbitrary ring homomorphism of fields (hence injective).
--
--   This records that the property of a $j$-invariant being supersingular, as formalised by vanishing of $q$-torsion in the group of rational points, is insensitive to the base field once it is known over an algebraically closed field: it ascends along any embedding of an algebraically closed field of characteristic $q$ into an arbitrary field of the same characteristic. It is the transfer step used throughout the study of supersingular points on modular curves in this development, in particular in the results locating maximal ideals with supersingular reduction on various level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_ssJSet_map_of_isAlgClosed
    {q : ℕ} [Fact q.Prime] {k₀ k : Type*} [Field k₀] [Field k] [CharP k₀ q] [CharP k q]
    [IsAlgClosed k₀] [DecidableEq k₀] [DecidableEq k]
    (θ : k₀ →+* k) (a : k₀) (ha : a ∈ ssJSet q k₀) : θ a ∈ ssJSet q k := by sorry
