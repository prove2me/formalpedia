-- Prove2me | Theorems.Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
-- name    : ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/e9a8dcd0-e359-50d2-91fa-48d29bd1d918
-- title:
--   ̃ j - a is a uniformiser when q ≤ 3
-- statement:
--   Let $q$ be a prime, let $k$ be an algebraically closed field of characteristic $q$, and let $N$ be a positive natural number with $q \nmid N$, and assume further that $q \le 3$. Write $F =$ `modularFunctionFieldC k N` for the intermediate field of the Laurent series field $k((X))$ obtained by adjoining to $k$ the two series `jqModC k` and `jqNModC k N`, the latter being the $N$-fold rescaling of the former, and let $\tilde j =$ `jGeomGen k N` denote `jqModC k` $=X^{-1}\cdot \mathrm{jNum}$ regarded as an element of $F$. Let $v$ be a place of $F$ over $k$, that is, a valuation subring of $F$ containing $k$, distinct from $F$ itself and a principal ideal ring. Suppose the value $v.\mathrm{evalAt}(\tilde j)$ — the image of $\tilde j$ in the residue field of $v$, pulled back to $k$ along the structural map, when $\tilde j$ lies in the valuation subring, and $0$ otherwise — equals $a \in k$, and that $a \ne 0$ and $a \ne 1728$. Then $v.\mathrm{ord}(\tilde j - a) = 1$, the order being $-\log$ of the adic valuation attached to $v$. Since $1728 = 0$ in $k$ here, the two conditions on $a$ exclude a single value.
--
--   The assertion is that $\tilde j - a$ is a uniformiser at $v$, i.e. that the covering $X_0(N)_k \to X(1)_k$ is unramified over the point $j = a$; this is the characteristic $2$ and $3$ case, where the two excluded $j$-invariants $0$ and $1728$ coincide. It feeds into [`ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq`](thm.html#ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq), which states the same conclusion for every characteristic prime to $N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.ord_jGeomGen_sub_algebraMap_eq_one_of_evalAt_eq_of_le_three
    (q : ℕ) [Fact q.Prime] (k : Type*) [Field k] [CharP k q] [IsAlgClosed k]
    (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N) (hq : q ≤ 3)
    (v : Place k ↥(modularFunctionFieldC k N))
    (a : k) (ha : v.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    v.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) = 1 := by sorry
