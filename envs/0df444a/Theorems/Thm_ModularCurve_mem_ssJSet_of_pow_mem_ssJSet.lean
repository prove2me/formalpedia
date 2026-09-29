-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet
-- name    : ModularCurve.mem_ssJSet_of_pow_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/3c1109c6-a583-5f39-a239-5d316c8dd3be
-- title:
--   Supersingularity of j from that of j^{p^e}
-- statement:
--   Let $p$ be a prime, let $K$ be a field of characteristic $p$, let $e$ be a natural number and let $j \in K$. Here $\mathrm{ssJSet}\,p\,K$ denotes the set of those $j' \in K$ with the property that for every Weierstrass curve $W$ over $K$ which is elliptic and satisfies $W.j = j'$, every point $P$ of the affine Weierstrass point group of $W$ with $p \cdot P = 0$ is the zero point; that is, no elliptic Weierstrass curve over $K$ with $j$-invariant $j'$ has a non-zero $K$-rational $p$-torsion point. The assertion is that if $j^{p^e}$ lies in $\mathrm{ssJSet}\,p\,K$, then $j$ lies in $\mathrm{ssJSet}\,p\,K$. No perfectness or algebraic closedness of $K$ is assumed, and the conclusion is about $K$-rational $p$-torsion only, rather than about supersingularity in the geometric sense.
--
--   This is the stability of the set of ($K$-rationally $p$-torsion-free) $j$-invariants under extraction of $p^e$-th roots, reflecting the fact that a curve and its $p^e$-power Frobenius twist are supersingular together. It is used in the analysis of supersingular points on modular curves, where $j$-invariants arising from charts or Tate parameters have to be recognised as supersingular after a Frobenius twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_of_pow_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_ssJSet_of_pow_mem_ssJSet
    (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [DecidableEq K] [CharP K p]
    (e : ℕ) (j : K) (h : j ^ (p ^ e) ∈ ssJSet p K) : j ∈ ssJSet p K := by sorry
