-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_theorem_5_corrected
-- name    : LargeBSP.Homog.Supplement.theorem_5_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:56:51.647808+00:00
-- url     : https://prove2.me/theorems/98f56e9e-4ec1-42c9-bef5-1f83b07b8e67
-- title:
--   Theorem 5, p. 21 (corrected: h(0) ≥ 0, positive surplus) — a budget-free menu is optimal for unknown budgets
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with finite mean whose distribution function $F_X$ satisfies (6), and let every item cost $c\ge0$, with $\mathbb E[(X_1-c)^+]>0$. The customer has budget $b_N>0$ with $b_N/N\to\bar b>0$. Let $g(N)/\sqrt N\to\infty$ and $g(N)=o(N)$, and let $h$ be continuous and strictly increasing on $[0,1]$ with $h(0)\ge0$. Put $t^\star=\sup\{s:F_X^{-1}(1-s)\ge c\}$, $\bar V(t)=\int_0^tF_X^{-1}(1-s)\,ds$ and, for $t=n/N$,
--   $$p_N(n)=\begin{cases}N\bar V(t)-h(t)g(N),&t\le t^\star,\\+\infty,&t>t^\star.\end{cases}$$
--   The customer buys the surplus-maximizing size among those that are affordable. Then
--   $$\lim_{N\to\infty}\frac{\mathbb E[\pi(p_N,b_N)]}{\mathbb E[\max_{n=0,\dots,N}(V_N(n)\wedge b_N-nc)]}=1,$$
--   and $\{p_N\}$ is asymptotically optimal: the ratio of $\mathbb E[\pi(p_N,b_N)]$ to the optimal budget-constrained profit tends to $1$.
--
--   A single menu, which does not use the budget, thus earns to first order as much as a seller who knows it.
--
--   **Formalization Note** As on the page, $p_N$ is a real-valued menu, and its prices at very small sizes may be negative. The optimum it is compared with is over nonnegative menus. The $\omega_+$ condition is divergence of $g(N)/\sqrt N$ to $+\infty$.
--
--   Differences from the source:
--
--   - encoding: items and order statistics are indexed from 1, ties between equally good sizes are unspecified, and ⇒ denotes a limit → items are indexed from 0, the customer takes the smallest of equally good sizes, and ⇒ is convergence in probability; reason: these are the conventions of the mission's model, and every limit here is a constant
--   - correction: h is any strictly increasing continuous function → also h(0) ≥ 0, equivalently h(t) > 0 for all t in (0,1]; reason: with X_n = 1, c = 0, b_N = N, h(t) = t − 2 and g(N) = N^(3/4) every price exceeds the bundle value and the ratio is 0; whenever h(0) < 0 the claim fails for small enough budgets, so exactly the functions with h(0) < 0 are excluded
--   - correction: the ratio (25) tends to 1 with no restriction on the surplus → E[(X_1 − c)^+] > 0; reason: otherwise the benchmark is identically 0 and the ratio is undefined; those cases are excluded
--   - reading: p_N(⌊Nt⌋) is given by a formula in real t → the formula is evaluated at t = n/N for each size n, and size 0 is the free no-purchase option; reason: a menu has one price for each size, and §5.3 sets p(0) = 0
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Theorem 5, p. 21; §5.3, p. 20; (6), p. 9; proof pp. A9–A10

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Costs
import Definitions.Def_LargeBSP_Homog_Supplement_Budget

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Theorem 5, p. 21, corrected by `h(0) ≥ 0` (for strictly increasing continuous `h`: positive discounts
at every positive size) and a positive limiting surplus. The budget-independent menu is evaluated on
the grid `t = n/N`; both (25) and asymptotic optimality (10) are stated. -/
theorem theorem_5_corrected {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (htail : TailCondition ν)
    (c : ℝ) (hc : 0 ≤ c) (b : ℕ → ℝ) (bbar : ℝ)
    (hb : ∀ N, 0 < b N) (hbbar : 0 < bbar)
    (hblim : Tendsto (fun N : ℕ => b N / (N : ℝ)) atTop (𝓝 bbar))
    (g : ℕ → ℝ) (h : ℝ → ℝ)
    (hgω : Tendsto (fun N : ℕ => g N / Real.sqrt N) atTop atTop)
    (hgo : Asymptotics.IsLittleO atTop g (fun N : ℕ => (N : ℝ)))
    (hhmono : StrictMonoOn h (Set.Icc 0 1)) (hhcont : ContinuousOn h (Set.Icc 0 1))
    (hh0 : 0 ≤ h 0) (hsurplus : 0 < ∫ x, max (x - c) 0 ∂ν) :
    Tendsto (fun N : ℕ =>
      budgetExpProfit P X c N (scalingBudgetMenu ν c g h N) (b N) /
      budgetBenchmark P X c N (b N)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ =>
      budgetExpProfit P X c N (scalingBudgetMenu ν c g h N) (b N) /
      budgetOptProfit P X c N (b N)) atTop (𝓝 1) := by sorry

end LargeBSP.Homog.Supplement
