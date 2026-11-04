-- Prove2me | Theorems.Thm_LostSalesExpGap_ConstOrder_theorem_1
-- name    : LostSalesExpGap.ConstOrder.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:33.435165+00:00
-- url     : https://prove2.me/theorems/a82296fc-c6a6-4a5e-8a74-37d1f1fd04c3
-- title:
--   Theorem 1, p. 8 — C(π_r∞)/OPT(L) ≤ 1 + h((1−γ)g)⁻¹(E[D] − r∞ + (eϑ(L+1))⁻¹)γ^{L+1}
-- statement:
--   Consider the periodic-review lost-sales inventory model: demands $D_1,D_2,\dots$ are i.i.d. copies of a nonnegative random variable $D$ with finite mean and strictly positive variance, the lead time is $L\ge1$, $h>0$ is the unit holding cost and $p>0$ the unit lost-sales penalty, and the system starts empty. Let $C(\pi)$ be the long-run average cost of a policy $\pi$ and $\mathrm{OPT}(L)=\inf_\pi C(\pi)$. Let $r_\infty$ be the best constant order (the least minimizer of $C(\pi_r)$ over $0\le r\le\mathbb E[D]$), and
--   $$
--   \gamma=\inf_{\theta\ge0}e^{\theta r_\infty}\mathbb E[e^{-\theta D}],\qquad g=\inf_{x\in\mathbb R}\mathbb E\big[h(x-D)^++p(x-D)^-\big],
--   $$
--   with $\vartheta$ the largest minimizer in the definition of $\gamma$ ($\vartheta=\infty$ if the infimum is not attained, and $1/\infty=0$). Then for all $L\ge1$,
--   $$
--   \frac{C(\pi_{r_\infty})}{\mathrm{OPT}(L)}\le1+h\big((1-\gamma)g\big)^{-1}\Big(\mathbb E[D]-r_\infty+\big(e\vartheta(L+1)\big)^{-1}\Big)\gamma^{L+1}.
--   $$
--
--   Since $\gamma<1$ and $r_\infty,\gamma,\vartheta,g$ do not depend on $L$, the optimality gap of the best constant-order policy decays exponentially in the lead time.
--
--   **Formalization Note** The model is the published `CappedBaseStock` model (zero-based time, empty initial state, costs in $[0,\infty]$). $\mathrm{OPT}(L)$ ranges over all measurable history-dependent randomized policies, a class containing the paper's Markov deterministic class $\Pi$, so the bound is at least as strong as printed. The ratio is taken in $[0,\infty]$, where $x/0=\infty$ for $x\neq0$. $(e\vartheta(L+1))^{-1}$ is written $\vartheta^{-1}/(e(L+1))$ with $\vartheta^{-1}=0$ when $\vartheta=\infty$. That $\gamma<1$ and $g>0$ are separate milestones, not hypotheses. Strictly positive variance is encoded as "not a point mass".
-- source:
--   Xin, Goldberg, Optimality gap of constant-order policies decays exponentially in the lead time for lost sales models, arXiv:1409.1499v2, Theorem 1, eq. (4), p. 8

import Mathlib
import Definitions.Def_LostSalesExpGap_ConstOrder_ConstantOrder

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LostSalesExpGap.ConstOrder

/-- Theorem 1 (Exponential convergence of constant-order policy to optimality), eq. (4), p. 8:
for every lead time `L ≥ 1`,
`C(π_{r∞}) / OPT(L) ≤ 1 + h((1 − γ)g)⁻¹ (E[D] − r∞ + (eϑ(L + 1))⁻¹) γ^{L+1}`,
with `1/ϑ = 0` when `ϑ = ∞`. The ratio is taken in `[0, ∞]`. -/
theorem theorem_1 (P : CappedBaseStock.DemandLaw) (c : CappedBaseStock.Parameters)
    (hP : LostSalesConstantOrder.LargeLeadTime.NonDeterministic P) :
    constCost P c (rInf P c) / CappedBaseStock.OPT P c ≤
      ENNReal.ofReal (1 + c.h * ((1 - gamma P c) * gNV P c)⁻¹ *
        ((CappedBaseStock.mean P - rInf P c) + varthetaInv P c / (Real.exp 1 * ((c.L : ℝ) + 1))) *
        gamma P c ^ (c.L + 1)) := by sorry

end LostSalesExpGap.ConstOrder
