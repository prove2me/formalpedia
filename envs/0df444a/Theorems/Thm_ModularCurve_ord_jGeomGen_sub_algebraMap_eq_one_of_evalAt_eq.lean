-- Prove2me | Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
-- name    : ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6b542089-2336-533b-b008-f35257c1ded6
-- title:
--   Geometric j is a uniformiser where j ≠ 0, 1728
-- statement:
--   Let $q$ be a prime number, $k$ an algebraically closed field of characteristic $q$, and $N$ a nonzero natural number with $q \nmid N$. Inside the field of Laurent series over $k$ let $j$ denote `jqModC k N`, the Laurent series $q^{-1}$ times the image of the integral power series `jNum` under $\mathbb{Z} \to k$, and let `modularFunctionFieldC k N` be the intermediate field obtained by adjoining to $k$ the two elements `jqModC k` and its $N$-fold $q$-expansion `jqNModC k N`; `jGeomGen k N` is the element of this field determined by `jqModC k`. Let $v$ be a place of `modularFunctionFieldC k N` over $k$, that is, a valuation subring of this field which contains the image of $k$, is not the whole field, and is a principal ideal ring. Assume the evaluation of `jGeomGen k N` at $v$ — the preimage under $k \to$ (residue field of $v$) of the residue of `jGeomGen k N` if the latter lies in the valuation subring, and $0$ otherwise — equals an element $a \in k$ with $a \neq 0$ and $a \neq 1728$. Then the order at $v$ of $j - a$, namely $-\log$ of the value of the associated height-one-spectrum adic valuation on `jGeomGen k N` $- \, a$, equals $1$.
--
--   This is the statement that the covering of the $j$-line by the level-$N$ modular curve over $k$ is unramified above every $j$-value outside $\{0, 1728\}$, in any characteristic prime to $N$: equivalently, $j - a$ is a uniformiser at each place above such an $a$. It converts the $j$-value form of the disc-parameter statements into the order-one form, and is used in the results on the orders of $j$ at places attached to the Hecke correspondences and in the prolongation-tuple reduction statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (v : Place k ↥(modularFunctionFieldC k N))
    (a : k) (ha : v.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) = 1 := by sorry
