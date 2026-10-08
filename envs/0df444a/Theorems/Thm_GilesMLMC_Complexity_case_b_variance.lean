-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_case_b_variance
-- name    : GilesMLMC.Complexity.case_b_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:33.268126+00:00
-- url     : https://prove2.me/theorems/0fa65729-4219-4b2d-9430-8126e173b9af
-- title:
--   Case (b), $\beta>1$ — with the case (b) sample sizes, $V[\widehat Y]<\tfrac12\varepsilon^2$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $M\ge2$ an integer, $T>0$, $h_l=M^{-l}T$, $\beta>1$ and $c_2>0$. Let $\widehat Y_l^{(n)}$ be square-integrable level estimators satisfying
--
--   1. (iii) $V[\widehat Y_l^{(n)}]\le c_2\,n^{-1}h_l^\beta$ for every $l$ and $n\ge1$;
--   2. for every choice of sample sizes $N_0,N_1,\dots\ge1$ the estimators $\widehat Y_l^{(N_l)}$ are independent.
--
--   Let $\varepsilon>0$, $L\ge0$, and
--   $$N_l=\Big\lceil2\varepsilon^{-2}c_2T^{(\beta-1)/2}\big(1-M^{-(\beta-1)/2}\big)^{-1}h_l^{(\beta+1)/2}\Big\rceil .$$
--   Then $\sum_{l=0}^LV[\widehat Y_l]\le\tfrac12\varepsilon^2T^{-(\beta-1)/2}(1-M^{-(\beta-1)/2})\sum_{l=0}^Lh_l^{(\beta-1)/2}$, and hence, by (8), the multilevel estimator $\widehat Y=\sum_{l=0}^L\widehat Y_l^{(N_l)}$ satisfies
--   $$V[\widehat Y]<\tfrac12\varepsilon^2 .$$
--
--   **Formalization Note** $P$ and $\widehat P_l$ are arbitrary random variables; in the paper they come from an SDE and its discretisation, which the theorem uses only through (i)–(iv). This makes the statement more general, not weaker. Each hypothesis on $\widehat Y_l$ is assumed for every sample size $N\ge1$, because the proof chooses the sample sizes; $\widehat Y_l$ is assumed square integrable (Lean's `variance` is $0$ off $L^2$). Independence of the level estimators is assumed for every choice of sample sizes $N_0,N_1,\dots\ge1$ (mutual independence). The bound is strict because (8) is strict, and it holds for every level $L$.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (b), variance, p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Case (b) of the proof of Theorem 3.1, variance (Giles 2008, §3, p. 610, PDF 4, left column): for `β > 1` and `N_l = ⌈2ε⁻²c₂T^{(β−1)/2}(1 − M^{−(β−1)/2})⁻¹h_l^{(β+1)/2}⌉`, `Σ V[Ŷ_l] ≤ ½ε²T^{−(β−1)/2}(1 − M^{−(β−1)/2}) Σ h_l^{(β−1)/2}`, and hence, with (8), a ½ε² upper bound on the variance of the estimator.

Formalization Note. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples; the paper's `P`, `P̂_l` come from an SDE and its discretisation, which the theorem uses only through (i)–(iv), so here they are arbitrary random variables (more general, not weaker). Hypotheses are assumed for every sample size `n ≥ 1` because the proof chooses the sample sizes; `MemLp 2` is needed because `variance` is 0 off L². Independence of the level estimators is assumed for every choice of sample sizes. The bound is strict, as it follows from the strict inequality (8). It holds for every `L : ℕ`. -/
theorem case_b_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β c₂ : ℝ) (hβ : 1 < β) (hc₂ : 0 < c₂)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ProbabilityTheory.variance (estimator Y (NB M T β c₂ ε) L) μ < ε ^ 2 / 2 := by sorry

end GilesMLMC.Complexity
