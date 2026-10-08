-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_case_a_variance
-- name    : GilesMLMC.Complexity.case_a_variance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:24:25.607308+00:00
-- url     : https://prove2.me/theorems/4ef67f0c-60f6-4f10-b665-411063aeacbd
-- title:
--   Case (a), $\beta=1$ — with $N_l=\lceil2\varepsilon^{-2}(L+1)c_2h_l\rceil$, $V[\widehat Y]\le\tfrac12\varepsilon^2$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space, $M\ge2$ an integer, $T>0$, $h_l=M^{-l}T$, $\beta=1$ and $c_2>0$. Let $\widehat Y_l^{(n)}$ be square-integrable level estimators, for every level $l$ and sample size $n\ge1$, such that
--
--   1. (iii) $V[\widehat Y_l^{(n)}]\le c_2\,n^{-1}h_l^\beta$ for every $l$ and $n\ge1$;
--   2. for every choice of sample sizes $N_0,N_1,\dots\ge1$ the estimators $\widehat Y_0^{(N_0)},\widehat Y_1^{(N_1)},\dots$ are independent.
--
--   Let $\varepsilon>0$, $L\ge0$, and $N_l=\lceil2\varepsilon^{-2}(L+1)c_2h_l\rceil$. Then the multilevel estimator $\widehat Y=\sum_{l=0}^L\widehat Y_l^{(N_l)}$ satisfies
--   $$V[\widehat Y]=\sum_{l=0}^LV[\widehat Y_l]\le\sum_{l=0}^Lc_2N_l^{-1}h_l\le\tfrac12\varepsilon^2 .$$
--
--   This is the variance half of the MSE bound in case (a).
--
--   **Formalization Note** $P$ and $\widehat P_l$ are arbitrary random variables; in the paper they come from an SDE and its discretisation, which the theorem uses only through (i)–(iv). This makes the statement more general, not weaker. Each hypothesis on $\widehat Y_l$ is assumed for every sample size $N\ge1$, because the proof chooses the sample sizes; $\widehat Y_l$ is assumed square integrable (Lean's `variance` is $0$ off $L^2$). Independence of the level estimators is assumed for every choice of sample sizes $N_0,N_1,\dots\ge1$ (mutual independence). The bound holds for every level $L$.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (a), p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup
import Definitions.Def_GilesMLMC_Complexity_Choices

namespace GilesMLMC.Complexity

/-- Case (a) of the proof of Theorem 3.1, variance (Giles 2008, §3, p. 609, PDF 3, right column): if `β = 1` and `N_l = ⌈2ε⁻²(L+1)c₂h_l⌉`, then `V[Ŷ] = Σ V[Ŷ_l] ≤ Σ c₂ N_l⁻¹ h_l ≤ ½ ε²`.

Formalization Note. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples; the paper's `P`, `P̂_l` come from an SDE and its discretisation, which the theorem uses only through (i)–(iv), so here they are arbitrary random variables (more general, not weaker). Hypotheses are assumed for every sample size `n ≥ 1` because the proof chooses the sample sizes; `MemLp 2` is needed because `variance` is 0 off L². Independence of the level estimators is assumed for every choice of sample sizes. The statement holds for every level `L : ℕ`. `Nat.ceil` agrees with `⌈·⌉` since its argument is positive. -/
theorem case_a_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β c₂ : ℝ) (hβ : β = 1) (hc₂ : 0 < c₂)
    (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ)
    (ε : ℝ) (hε : 0 < ε) (L : ℕ) :
    ProbabilityTheory.variance (estimator Y (NA M T c₂ ε L) L) μ ≤ ε ^ 2 / 2 := by sorry

end GilesMLMC.Complexity
