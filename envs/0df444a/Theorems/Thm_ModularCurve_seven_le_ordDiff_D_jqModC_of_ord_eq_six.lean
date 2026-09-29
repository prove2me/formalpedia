-- Prove2me | Theorems.Thm_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six
-- name    : ModularCurve.seven_le_ordDiff_D_jqModC_of_ord_eq_six
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/37ee0487-0db5-53a3-9ce6-27ac0ee3884f
-- title:
--   Different exponent ≥ 7 at a characteristic-3 place with ord_P(j)=6
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $3$ and let $N \ge 1$ be an integer whose image in $K$ is nonzero. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of $K((q))$ obtained by adjoining to $K$ the set of Laurent series $\mathrm{qExpand}_K(d)(j_q)$ for the divisors $d \mid N$ with $d \neq 0$, where $j_q = q^{-1}\cdot(E_4^3\,\eta^{-24})$ is the image in $K((q))$ of the integral $q$-expansion `jqModC`; the element $j_q$ itself lies in $F$. Let $P$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring, and let $\mathrm{ord}_P$ be the associated normalised integer-valued order function. Assume $\mathrm{ord}_P(j_q) = 6$. Then $\mathrm{ord}_P$ of the Kähler differential $\mathrm{d}j_q \in \Omega_{F/K}$ is at least $7$, where the order of a differential $\omega$ means $\mathrm{ord}_P(g)$ for a chosen $g \in F$ with $\omega = g\,\mathrm{d}t$ and $t$ a chosen element with $\mathrm{ord}_P(t) = 1$.
--
--   This is the local contribution of a wildly ramified supersingular point to the different of the $j$-map on the modular curve of level $N$ in characteristic $3$: at a place where $j$ vanishes to order $6$ the different exponent is bounded below by $7$ rather than by the tame value $5$. It feeds the global estimate [`ModularCurve.le_six_mul_sum_ordDiff_D_jqModC_of_lt_five`](thm.html#ModularCurve.le_six_mul_sum_ordDiff_D_jqModC_of_lt_five), where sums of such local exponents are compared with the degree of the canonical class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.seven_le_ordDiff_D_jqModC_of_ord_eq_six
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K 3] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (P : Place K (modularFunctionFieldFullC K N))
    (hP : P.ord (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N) = 6) :
    7 ≤ P.ordDiff (KaehlerDifferential.D K (modularFunctionFieldFullC K N)
        (⟨jqModC K, jqModC_mem_full K N⟩ : modularFunctionFieldFullC K N)) := by sorry
