-- Prove2me | Theorems.Thm_IncProx_Randomized_proposition2
-- name    : IncProx.Randomized.proposition2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:55.337099+00:00
-- url     : https://prove2.me/theorems/9e615e9b-67f0-4246-a0c6-e49cd7da7399
-- title:
--   Proposition 2 — supermartingale convergence theorem: $E\{Y_{k+1}\mid\mathcal F_k\}\le Y_k-Z_k+W_k$, $\sum W_k<\infty$ ⇒ $\sum Z_k<\infty$, $Y_k$ converges
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space with a filtration $\mathcal F_0\subseteq\mathcal F_1\subseteq\cdots\subseteq\mathcal F$, and let $Y_k,Z_k,W_k$, $k=0,1,\dots$, be real random variables such that:
--   1. $Y_k$, $Z_k$, $W_k$ are nonnegative and $\mathcal F_k$-measurable;
--   2. for each $k$, almost surely,
--   $$E\{Y_{k+1}\mid\mathcal F_k\}\le Y_k-Z_k+W_k;$$
--   3. with probability 1, $\sum_{k=0}^\infty W_k<\infty$.
--
--   Then, with probability 1, $\sum_{k=0}^\infty Z_k<\infty$, and the sequence $Y_k$ converges to a nonnegative (finite) random variable $Y$.
--
--   This is the special case of the Robbins–Siegmund theorem that the paper cites from the literature and uses in the analysis of the randomized methods: applied with $Y_k=\|x_k-x^*\|^2$ it turns the conditional descent inequality (58) into the almost sure statement (59).
--
--   **Formalization Note** The paper's "sets of random variables $\mathcal F_k\subset\mathcal F_{k+1}$" are read as the $\sigma$-algebras they generate, i.e. a filtration, and "functions of the random variables in $\mathcal F_k$" as adaptedness. Integrability of each $Y_k$ is an added hypothesis: Lean's conditional expectation of a non-integrable function is $0$, so without it condition 2 would not express the paper's inequality. In the application $Y_k$ is integrable. Nonnegativity is required pointwise.
-- source:
--   Bertsekas, Incremental Proximal Methods for Large Scale Convex Optimization, LIDS-P-2847 (rev. March 2011), p. 8, Proposition 2

import Mathlib

namespace IncProx.Randomized

open Filter Topology MeasureTheory

/-- Proposition 2 (Supermartingale Convergence Theorem, p. 8). `Y`, `Z`, `W` are nonnegative and
adapted to the filtration `𝓕` (F_k ⊂ F_{k+1}); `E{Y_{k+1} | F_k} ≤ Y_k − Z_k + W_k`;
`Σ W_k < ∞` with probability 1. Then with probability 1 `Σ Z_k < ∞` and `Y_k` converges to a
nonnegative random variable. Integrability of each `Y_k` is an added hypothesis (Lean's conditional
expectation of a non-integrable function is `0`). -/
theorem proposition2 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (𝓕 : Filtration ℕ m0) (Y Z W : ℕ → Ω → ℝ)
    (hYad : Adapted 𝓕 Y) (hZad : Adapted 𝓕 Z) (hWad : Adapted 𝓕 W)
    (hY0 : ∀ k s, 0 ≤ Y k s) (hZ0 : ∀ k s, 0 ≤ Z k s) (hW0 : ∀ k s, 0 ≤ W k s)
    (hYint : ∀ k, Integrable (Y k) μ)
    (h2 : ∀ k, μ[Y (k + 1) | 𝓕 k] ≤ᵐ[μ] fun s => Y k s - Z k s + W k s)
    (h3 : ∀ᵐ s ∂μ, Summable fun k => W k s) :
    (∀ᵐ s ∂μ, Summable fun k => Z k s) ∧
      ∃ Yinf : Ω → ℝ, Measurable Yinf ∧
        ∀ᵐ s ∂μ, 0 ≤ Yinf s ∧ Tendsto (fun k => Y k s) atTop (𝓝 (Yinf s)) := by sorry

end IncProx.Randomized
