-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_theorem_3_1
-- name    : GilesMLMC.Complexity.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:45.727646+00:00
-- url     : https://prove2.me/theorems/bcb5bcf7-ac19-4770-ab26-a53faeb0439a
-- title:
--   Theorem 3.1 — the multilevel estimator reaches MSE $<\varepsilon^2$ at cost $c_4\varepsilon^{-2}$, $c_4\varepsilon^{-2}(\log\varepsilon)^2$ or $c_4\varepsilon^{-2-(1-\beta)/\alpha}$
-- statement:
--   **Complexity theorem for multilevel Monte Carlo.** Let $(\Omega,\mathcal F,\mu)$ be a probability space, $P$ an integrable random variable (in the paper, a functional of the solution of an SDE for a given Brownian path) and $\widehat P_l$, $l\ge0$, integrable random variables (its approximations with timestep $h_l=M^{-l}T$, where $M\ge2$ is an integer and $T>0$). For every level $l$ and every sample size $n\ge1$ let $\widehat Y_l^{(n)}$ be a square-integrable estimator based on $n$ Monte Carlo samples, with computational complexity $C_l^{(n)}$. Suppose there are constants $\alpha\ge\frac12$ and $\beta,c_1,c_2,c_3>0$ such that, for every $l$ and every $n\ge1$,
--
--   1. (i) $\big|E[\widehat P_l-P]\big|\le c_1h_l^\alpha$;
--   2. (ii) $E[\widehat Y_l^{(n)}]=E[\widehat P_0]$ if $l=0$, and $E[\widehat Y_l^{(n)}]=E[\widehat P_l-\widehat P_{l-1}]$ if $l>0$;
--   3. (iii) $V[\widehat Y_l^{(n)}]\le c_2\,n^{-1}h_l^\beta$;
--   4. (iv) $C_l^{(n)}\le c_3\,n\,h_l^{-1}$;
--
--   and that for every choice of sample sizes $N_0,N_1,\dots\ge1$ the estimators $\widehat Y_l^{(N_l)}$ are independent. Then there is a constant $c_4>0$ such that for every $0<\varepsilon<e^{-1}$ there are a finest level $L$ and sample sizes $N_l\ge1$ for which the multilevel estimator $\widehat Y=\sum_{l=0}^L\widehat Y_l^{(N_l)}$ has
--   $$\mathrm{MSE}\equiv E\big[(\widehat Y-E[P])^2\big]<\varepsilon^2,$$
--   with a computational complexity $C=\sum_{l=0}^LC_l^{(N_l)}$ bounded by
--   $$C\le\begin{cases}c_4\varepsilon^{-2},&\beta>1,\\ c_4\varepsilon^{-2}(\log\varepsilon)^2,&\beta=1,\\ c_4\varepsilon^{-2-(1-\beta)/\alpha},&0<\beta<1.\end{cases}$$
--
--   Plain Monte Carlo with an Euler discretisation needs cost of order $\varepsilon^{-3}$ for the same accuracy; the theorem shows that the multilevel estimator reaches the cost $\varepsilon^{-2}$ of an unbiased estimator when $\beta>1$, loses only a factor $(\log\varepsilon)^2$ when $\beta=1$ (the Euler scheme with a Lipschitz payoff), and gives an explicit rate otherwise.
--
--   **Formalization Note** $P$ and $\widehat P_l$ are arbitrary random variables; in the paper they come from an SDE and its discretisation, which the theorem uses only through (i)–(iv). This makes the statement more general, not weaker. Hypotheses (ii)–(iv), square integrability and independence are assumed for every sample size $n\ge1$, because the theorem chooses the sample sizes. Hypothesis (i) carries an absolute value: the page prints the one-sided $E[\widehat P_l-P]\le c_1h_l^\alpha$, under which the theorem is false (take $E[\widehat P_l-P]=-1$ for every $l$); the proof uses the two-sided bound. $M\ge2$ is the paper's standing "integer $M\geqslant2$" (§1), $\varepsilon>0$ is implicit. The complexity $C$ is the sum of the level complexities, each constrained only by (iv). Since $\beta$ is fixed by the hypotheses, one constant $c_4$ serves; it does not depend on $\varepsilon$, $L$ or $N_l$.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), Theorem 3.1, §3, p. 609

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

namespace GilesMLMC.Complexity

/-- **Theorem 3.1** (Giles 2008, Multilevel Monte Carlo path simulation, Operations Research
56(3), §3, p. 609, PDF 3, left column).

Formalization Note. `P` and `Phat l` (= P̂_l) are arbitrary real random variables on a
probability space; in the paper they come from an SDE and its discretisation with timestep
`h_l = M^{-l} T`, which the theorem uses only through (i)–(iv), so the statement is more
general, not weaker. `Y l n` is the level-`l` estimator Ŷ_l built from `n` samples and
`cost l n` its computational complexity C_l; since the theorem chooses the sample sizes,
(ii)–(iv), square integrability and independence are assumed for every sample size `n ≥ 1`.
Hypothesis (i) carries an absolute value: the page prints `E[P̂_l − P] ≤ c₁ h_l^α`, which
would make the theorem false (take `E[P̂_l − P] = −1`); the proof uses the two-sided bound.
`P`, `P̂_l` are integrable and every `Ŷ_l` is in L² (otherwise `∫` and `variance` take
junk value 0). `M ≥ 2` is the paper's standing "integer M ⩾ 2" (§1, p. 607); `T > 0`; `ε > 0`
is implicit in "ε < e⁻¹". The computational complexity `C` of Ŷ is `Σ_{l=0}^L C_l`. Since `β` is
fixed by the hypotheses, one `c₄` serves; the three implications are the three cases of the
paper's display. Real powers are `Real.rpow`. -/
theorem theorem_3_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α β c₁ c₂ c₃ : ℝ) (hα : 1 / 2 ≤ α) (hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (P : Ω → ℝ) (Phat : ℕ → Ω → ℝ) (Y : ℕ → ℕ → Ω → ℝ) (cost : ℕ → ℕ → ℝ)
    (hP : MeasureTheory.Integrable P μ)
    (hPhat : ∀ l, MeasureTheory.Integrable (Phat l) μ)
    (hY : ∀ l N, 1 ≤ N → MeasureTheory.MemLp (Y l N) 2 μ)
    (h_i : ∀ l, |∫ ω, (Phat l ω - P ω) ∂μ| ≤ c₁ * h M T l ^ α)
    (h_ii : ∀ l N, 1 ≤ N → ∫ ω, Y l N ω ∂μ =
      if l = 0 then ∫ ω, Phat 0 ω ∂μ else ∫ ω, (Phat l ω - Phat (l - 1) ω) ∂μ)
    (h_iii : ∀ l N, 1 ≤ N →
      ProbabilityTheory.variance (Y l N) μ ≤ c₂ * (N : ℝ)⁻¹ * h M T l ^ β)
    (h_iv : ∀ l N, 1 ≤ N → cost l N ≤ c₃ * N * (h M T l)⁻¹)
    (h_indep : ∀ N : ℕ → ℕ, (∀ l, 1 ≤ N l) →
      ProbabilityTheory.iIndepFun (fun l => Y l (N l)) μ) :
    ∃ c₄ : ℝ, 0 < c₄ ∧ ∀ ε : ℝ, 0 < ε → ε < Real.exp (-1) →
      ∃ (L : ℕ) (N : ℕ → ℕ), (∀ l, 1 ≤ N l) ∧
        mse μ (estimator Y N L) P < ε ^ 2 ∧
        (1 < β → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ)) ∧
        (β = 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 : ℝ) * Real.log ε ^ 2) ∧
        (β < 1 → totalCost cost N L ≤ c₄ * ε ^ (-2 - (1 - β) / α)) := by sorry

end GilesMLMC.Complexity
