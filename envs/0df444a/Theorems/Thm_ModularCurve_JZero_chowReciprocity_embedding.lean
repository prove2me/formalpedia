-- Prove2me | Theorems.Thm_ModularCurve_JZero_chowReciprocity_embedding
-- name    : ModularCurve.JZero.chowReciprocity_embedding
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7945707e-cea2-5fc0-b03f-280e89c8ad17
-- title:
--   Chow reciprocity for sections of the embedding divisor
-- statement:
--   Let $N$ be a nonzero natural number and let $F =$ `modularFunctionFieldBar N` be the level-$N$ modular function field base-changed to $\bar{\mathbb Q} =$ `AlgebraicClosure ℚ`, viewed inside Laurent series over $\bar{\mathbb Q}$. Let $E =$ `embDivisor N` $= (2g+1)\cdot[\infty]$, where $g$ is the genus of $F$ over $\bar{\mathbb Q}$ and $\infty$ is the cusp place `cuspInftyBar N`. Let $s : \mathrm{Fin}\,r \to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\bar{\mathbb Q}$ and spans the Riemann–Roch space of $E$ (the functions $f$ with $v(f) \le \exp(E\,v)$ at every place $v$). Let $k$ be a natural number and $u \in F$ be nonzero and lie in the Riemann–Roch space of $k\cdot E$, and let $B$ be a divisor with $B\,w = \mathrm{ord}_w(u) + k\,(E\,w)$ at every place $w$, where $\mathrm{ord}_w$ is minus the logarithm of the adic valuation at $w$. The conclusion is `ChowReciprocity s E k u B`: for all coefficient vectors $a,b,c : \mathrm{Fin}\,r \to \bar{\mathbb Q}$ with the linear sections $\sum_i a_i s_i$, $\sum_i b_i s_i$, $\sum_i c_i s_i$ nonzero, and all divisors $Z_a, Z_b, Z_c$ given place-by-place by $Z_a\,w = \mathrm{ord}_w(\sum_i a_i s_i) + E\,w$ and likewise for $b$ and $c$, subject to the disjointness condition that at every place $w$ either $Z_a\,w = Z_b\,w = 0$ or $B\,w = Z_c\,w = 0$, one has
--   $$\mathrm{ev}_a(\mathrm{Ch}\,B)\cdot \mathrm{ev}_b(\mathrm{Ch}\,Z_c)^k\cdot \mathrm{ev}_c(\mathrm{Ch}\,Z_a)^k\cdot \mathrm{sp}(Z_b) = \mathrm{ev}_b(\mathrm{Ch}\,B)\cdot \mathrm{ev}_a(\mathrm{Ch}\,Z_c)^k\cdot \mathrm{ev}_c(\mathrm{Ch}\,Z_b)^k\cdot \mathrm{sp}(Z_a),$$
--   where $\mathrm{Ch}\,Z = \prod_w \bigl(\sum_i \mathrm{evalVec}(s,w)_i X_i\bigr)^{(Z\,w)^+}$ is the `chowForm` of a divisor $Z$, a polynomial in $X_0,\dots,X_{r-1}$ built from the evaluation vectors $\mathrm{evalVec}$ of the family $s$ at the places $w$, $\mathrm{ev}_a$ denotes evaluation of such a polynomial at $a$, and $\mathrm{sp}(Z) = \prod_w \mathrm{secVal}(s,w,k,u)^{(Z\,w)^+}$ is `secProd`, formed from the scalars $\mathrm{secVal}$ attached to $s$, $w$, $k$ and $u$; in both products the exponent is the truncation to $\mathbb N$ of the multiplicity.
--
--   This is the Weil-reciprocity identity in the form needed for the projective coordinates supplied by a basis of $L((2g+1)\infty)$ on the modular curve, comparing the Chow forms of the divisors of linear sections with those of the divisor of $u$. It is the multiplicative input to the archimedean Jensen-type estimate [`ModularCurve.JZero.jensen_arch_embedding`](thm.html#ModularCurve.JZero.jensen_arch_embedding) in the construction of the height form on $\mathrm{Pic}^0$ of the modular function field, and is deduced from [`AlgebraicCurve.weilReciprocity`](thm.html#AlgebraicCurve.weilReciprocity) together with the existence of principal divisors for `modularFunctionFieldBar N` and the rationality of all its places over the algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_chowReciprocity_embedding.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.chowReciprocity_embedding (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (k : ℕ) (u : modularFunctionFieldBar N)
    (hu : u ≠ 0) (huL : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ChowReciprocity s (embDivisor N) k u B := by sorry
