-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_theorem_B1_corrected
-- name    : LargeBSP.Homog.Supplement.theorem_B1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:59:46.841174+00:00
-- url     : https://prove2.me/theorems/c50cb395-1e31-422b-b890-82755b34c6c1
-- title:
--   Theorem B1, p. A14 (corrected: h(⌊b/η_F⌋) > 0; (B1) holds exactly when b − ⌊b/η_F⌋η_F ≤ c) — constant budgets
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with finite upper endpoint $\eta_F$ whose tail satisfies $1-F_X(\eta_F-1/x)=x^{-\alpha}L(x)$ for large $x$ ($\alpha>0$, $L$ slowly varying), and let every item cost $c\in[0,\eta_F)$. The budget is any constant $b$ with $\eta_F\le b\le K_b\eta_F$. Let $a_N=\eta_F-F_X^{-1}(1-1/N)$, let $d(N)/a_N\to\infty$ and $d(N)\to0$, let $h$ be strictly increasing on $\{1,\dots,K_b\}$ with $h(\lfloor b/\eta_F\rfloor)>0$, and let $p_N(n)=n\eta_F-h(n)d(N)$ for $n\le K_b$ and $+\infty$ otherwise. Put
--   $$k=\lfloor b/\eta_F\rfloor,\qquad r=b-k\eta_F,\qquad M=k(\eta_F-c),\qquad M^\star=M+(r-c)^+.$$
--   Then, as $N\to\infty$:
--
--   1. $\mathbb E[\pi(p_N,b)]\to M$;
--   2. the benchmark $\mathbb E[\max_{n=0,\dots,N}(V_N(n)\wedge b-nc)]$ and the optimal budget-constrained expected profit both tend to $M^\star$;
--   3. the ratio of $\mathbb E[\pi(p_N,b)]$ to each of them tends to $M/M^\star$;
--   4. the printed limit (B1) holds, that is, the ratio to the benchmark tends to $1$, if and only if $r\le c$.
--
--   The paper asserts the limit $1$ for every $b$ in the interval, which is false: for Uniform$[0,1]$ valuations, $c=0$, $K_b=2$, $b=3/2$, $h(n)=n$ and $d(N)=N^{-1/2}$ the limit is $2/3$. The corrected statement keeps the whole interval, gives the limit at each budget, and contains the paper's claim for all budgets $b=n\eta_F$ to which its proof reduces.
--
--   **Formalization Note** Choice and profit under the budget are those of (22)–(23), with the smallest size chosen among equally good ones. The optimum is a supremum over nonnegative menus.
--
--   Differences from the source:
--
--   - correction: the ratio (B1) tends to 1 and the menu is asymptotically optimal for every b in [η_F, K_b η_F] → both ratios tend to M/M⋆, and (B1) holds iff b − ⌊b/η_F⌋η_F ≤ c; reason: the proof treats n_b = b/η_F as an integer, and at Uniform[0,1], c = 0, K_b = 2, b = 3/2 the limit is 2/3; p. A14 itself notes that a seller who knows such a budget extracts all of b; no budget is excluded
--   - correction: h is any strictly increasing function → h is strictly increasing on {1,…,K_b} with h(⌊b/η_F⌋) > 0; reason: if h(⌊b/η_F⌋) ≤ 0 then every affordable size n ≤ ⌊b/η_F⌋ has surplus V_N(n) − nη_F + h(n)d(N) < 0 almost surely (no atom at η_F, h(n) ≤ h(⌊b/η_F⌋) ≤ 0) and larger sizes are eventually unaffordable, so the customer never buys and the profit is 0 while the benchmark tends to M⋆ > 0; exactly the pairs (h, b) with h(⌊b/η_F⌋) ≤ 0 are excluded. Over the whole interval of unknown budgets this is h(1) > 0
--   - reading: the theorem repeats only c ≥ 0 and the budget interval → the standing assumptions of Appendix B are bound: i.i.d. valuations, finite endpoint η_F > c, and the regularly varying tail; reason: Appendix B states them for the case b ≥ η_F immediately before the theorem and the proof uses them
--   - generalization: 1 − F_X(η_F − 1/x) = x^{-α} L(x), with no range of x given → the identity is required only for all sufficiently large x; reason: only the tail at the endpoint matters, so the Lean statement implies the printed one
--   - encoding: the sum in (B1) has an unclosed bracket and ties between sizes are unspecified → the benchmark is the expectation of the maximum and the customer takes the smallest of equally good sizes; reason: this is the benchmark (24) and the tie rule of the mission's model
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Theorem B1, (B1), p. A14; Appendix B, pp. A13–A15

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Budget
import Definitions.Def_LargeBSP_Homog_Supplement_Extremes

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Theorem B1, p. A14, corrected on the whole printed interval `η_F ≤ b ≤ K_b η_F`. With
`k = ⌊b/η_F⌋`, `r = b - k η_F` and a positive discount at size `k` (`h k > 0`), the menu earns
`k (η_F - c)` in the limit, the benchmark and the optimum exceed this by `(r - c)^+`, and the printed
limit 1 in (B1) holds exactly when `r ≤ c`. -/
theorem theorem_B1_corrected {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0)
    (hfinite : BddAbove {x : ℝ | cdf ν x < 1})
    (α : ℝ) (L : ℝ → ℝ) (htail : EndpointTail ν α L)
    (c : ℝ) (hc : 0 ≤ c) (hcη : c < endpoint ν)
    (Kb : ℕ) (b : ℝ) (hbl : endpoint ν ≤ b) (hbu : b ≤ (Kb : ℝ) * endpoint ν)
    (d : ℕ → ℝ) (hdω : Tendsto (fun N : ℕ => d N / extremeScale ν N) atTop atTop)
    (hdo : Tendsto d atTop (𝓝 0))
    (h : ℕ → ℝ) (hhmono : StrictMonoOn h (Set.Icc 1 Kb)) (hhk : 0 < h ⌊b / endpoint ν⌋₊) :
    let η : ℝ := endpoint ν
    let k : ℝ := (⌊b / η⌋₊ : ℝ)
    let r : ℝ := b - k * η
    let menuLimit : ℝ := k * (η - c)
    let bestLimit : ℝ := k * (η - c) + max (r - c) 0
    Tendsto (fun N : ℕ => budgetExpProfit P X c N (endpointMenu η Kb d h N) b)
      atTop (𝓝 menuLimit) ∧
    Tendsto (fun N : ℕ => budgetBenchmark P X c N b) atTop (𝓝 bestLimit) ∧
    Tendsto (fun N : ℕ => budgetOptProfit P X c N b) atTop (𝓝 bestLimit) ∧
    Tendsto (fun N : ℕ => budgetExpProfit P X c N (endpointMenu η Kb d h N) b /
      budgetBenchmark P X c N b) atTop (𝓝 (menuLimit / bestLimit)) ∧
    Tendsto (fun N : ℕ => budgetExpProfit P X c N (endpointMenu η Kb d h N) b /
      budgetOptProfit P X c N b) atTop (𝓝 (menuLimit / bestLimit)) ∧
    (Tendsto (fun N : ℕ => budgetExpProfit P X c N (endpointMenu η Kb d h N) b /
      budgetBenchmark P X c N b) atTop (𝓝 1) ↔ r ≤ c) := by sorry

end LargeBSP.Homog.Supplement
