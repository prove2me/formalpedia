-- Prove2me | Theorems.Thm_ModernConvex_Ellipsoids_nesterov_ye
-- name    : ModernConvex.Ellipsoids.nesterov_ye
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:50.496268+00:00
-- url     : https://prove2.me/theorems/e8ad933d-cce5-4d9d-941c-11e5a8d0a6a8
-- title:
--   Proposition 4.10.5 (Nesterov, Ye) — commuting Bᵢ, A ⪰ 0: F∗ ≤ (π/2) f∗
-- statement:
--   Consider the setting (SL.??). Symmetric $n\times n$ matrices $B_1,\dots,B_m$ and reals $d_1,\dots,d_m\ge0$ define the system $(S')$: $x^TB_ix\le d_i$, $i=1,\dots,m$. Let $f(x)=x^TAx$, let $f^*$ be the optimal value of $(P)$ $\max\{f(x) : x\text{ solves }(S')\}$, and let $F^*$ be the optimal value of
--   $$\max_X\big\{\operatorname{Tr}(AX) : \operatorname{Tr}(B_iX)\le d_i,\ i=1,\dots,m,\ X=X^T\succeq0\big\}.\qquad\text{(SDP)}$$
--   Assume:
--   1. the matrices $B_1,\dots,B_m$ commute with each other;
--   2. $(S')$ is strictly feasible, and some combination of the $B_i$ with nonnegative coefficients is positive definite;
--   3. $A\succeq0$.
--
--   Then $f^*\ge0$, and the dual $\min_\lambda\{\sum_i\lambda_id_i : \sum_i\lambda_iB_i\succeq A,\ \lambda\ge0\}$ (SDD) is solvable with optimal value $F^*$. Moreover,
--   $$F^*\le\frac{\pi}{2}\,f^*.\qquad(4.10.137)$$
--
--   In §4.9 this is the estimate behind the factor $(\pi/2)^{n/2}$ of Proposition 4.9.5.
--
--   **Formalization Note** $f^*$ and $F^*$ are given as reals together with the predicate that each is the least upper bound of its problem's objective over the feasible set. Under the hypotheses both values exist: $x=0$ and $X=0$ are feasible, and the positive definite combination bounds both feasible sets. The standing assumptions of (SL.??), $d_i\ge0$ and symmetric $B_i$, are explicit hypotheses. "Solvable with optimal value $F^*$" is attainment of the minimum. The statement restates, in this mission's namespace, the draft `ModernConvex.Relaxations.nesterov_ye` of the series' relaxations mission. A draft cannot import another mission's draft.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 314–315, Proposition 4.10.5

import Mathlib
import Definitions.Def_ModernConvex_Ellipsoids_Programs

open Matrix

namespace ModernConvex.Ellipsoids

/-- Ben-Tal–Nemirovski, Proposition 4.10.5 (Nesterov, Ye), pp. 314–315. Consider (SL.??) (p. 313):
symmetric `B₁, …, Bₘ`, all `dᵢ ≥ 0`, `f(x) = xᵀAx`, `f∗` the optimal value of (P) and `F∗` the
optimal value of (SDP). Assume
1. the matrices `B₁, …, Bₘ` commute with each other;
2. system (S′) is strictly feasible, and some combination of the `Bᵢ` with nonnegative
   coefficients is positive definite;
3. `A ⪰ 0`.
Then `f∗ ≥ 0`, (SDD) is solvable with the optimal value `F∗`, and `F∗ ≤ (π/2) f∗` (4.10.137). -/
theorem nesterov_ye {n m : ℕ} (S : QuadraticSystem n m)
    (hB : ∀ i, (S.B i).IsHermitian) (hd : ∀ i, 0 ≤ S.d i)
    (hcomm : ∀ i j, S.B i * S.B j = S.B j * S.B i)
    (hstrict : S.StrictlyFeasible)
    (hpd : ∃ μ : Fin m → ℝ, (∀ i, 0 ≤ μ i) ∧ (∑ i, μ i • S.B i).PosDef)
    (hA : S.A.PosSemidef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧ Fstar ≤ Real.pi / 2 * fstar := by sorry

end ModernConvex.Ellipsoids
