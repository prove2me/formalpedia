-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_degree_mul_baseHt_of_mem_riemannRochSpace
-- name    : ModularCurve.JZero.exists_pointHt_le_degree_mul_baseHt_of_mem_riemannRochSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/bf87f3fc-4192-5653-980b-560e85e7f204
-- title:
--   Upper bound h_f ≤ deg A (1+ε) t + C off the cusp
-- statement:
--   Fix $N \ge 1$ and work with the field $F =$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $N$ inside Laurent series. Let $s : \mathrm{Fin}\,r \to F$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its range spans the Riemann–Roch space of the divisor `embDivisor N` $= (\text{embDegree } N)\cdot \bar\infty$, where $\bar\infty =$ `cuspInftyBar N`; write $t(u) =$ `baseHt s (cuspInftyBar N) u`, which is $0$ at $u = \bar\infty$ and otherwise equals $\mathrm{pointHt}\,s\,u + \mathrm{pointHt}\,s\,\bar\infty - \mathrm{absLogHeight}(\mathrm{chordVec}\,s\,u\,\bar\infty)$. Let $A$ be a divisor, i.e. a finitely supported $\mathbb Z$-valued function on the places of $F$ over $\overline{\mathbb Q}$, with $\deg A > 0$ for the degree homomorphism weighting each place by its residue degree. Let $f : \mathrm{Fin}\,m \to F$ be a family with $f_j \ne 0$ for all $j$ and $f_j \in$ `riemannRochSpace A`, that is $v(f_j) \le \exp(A(v))$ for every place $v$. Then for every real $\varepsilon > 0$ there exists a real constant $C$ such that for every place $u \ne \bar\infty$,
--   $$\mathrm{pointHt}\,f\,u \;\le\; (\deg A)(1+\varepsilon)\, t(u) + C,$$
--   where $\mathrm{pointHt}\,f\,u$ is the normalised absolute logarithmic height of the pivot-normalised vector of values $\bigl(u(f_j/f_{\mathrm{piv}})\bigr)_j$.
--
--   This is the upper half of the comparison, in Weil's height machine on the curve $X_0(N)_{\overline{\mathbb Q}}$, between the height attached to an arbitrary nonzero family inside $L(A)$ and the base height coming from the chosen embedding basis: no completeness or base-point-freeness of the family $f$ is assumed, and only the inequality $\le \deg A\,(1+\varepsilon)\,t + C$ is asserted, for places away from the cusp $\bar\infty$. It feeds the height estimate [`ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le`](thm.html#ModularCurve.JZero.exists_absLogHeight_regVal_sub_two_mul_pointHt_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_pointHt_le_degree_mul_baseHt_of_mem_riemannRochSpace.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_pointHt_le_degree_mul_baseHt_of_mem_riemannRochSpace (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (A : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hA : 0 < A.degree)
    {m : ℕ} (f : Fin m → modularFunctionFieldBar N) (hf0 : ∀ j, f j ≠ 0)
    (hfA : ∀ j, f j ∈ riemannRochSpace A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), u ≠ cuspInftyBar N →
      pointHt f u ≤ (A.degree : ℝ) * (1 + ε) * baseHt s (cuspInftyBar N) u + C := by sorry
