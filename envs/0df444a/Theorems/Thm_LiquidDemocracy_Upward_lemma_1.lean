-- Prove2me | Theorems.Thm_LiquidDemocracy_Upward_lemma_1
-- name    : LiquidDemocracy.Upward.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:41.283363+00:00
-- url     : https://prove2.me/theorems/d798b4c0-9990-406b-8f78-991713c29b13
-- title:
--   Lemma 1, p. 11 — core lemma: (1) and (2) imply probabilistic do no harm; with (3) also probabilistic positive gain
-- statement:
--   Let $M=(q,\varphi)$ be a model and $\mathfrak D$ a class of distributions supported in $[0,1]$. Suppose that for every $\mathcal D\in\mathfrak D$ there are $\alpha\in(0,1)$ and $C:\mathbb N\to\mathbb N$ with $C(n)\in o(n)$ such that, as $n\to\infty$,
--
--   $$\mathbb P_{\mathcal D,M,n}\big[\text{max-weight}(G_n)\le C(n)\big]=1-o(1),\qquad(1)$$
--   $$\mathbb P_{\mathcal D,M,n}\Big[\sum_{i=1}^n\mathrm{weight}_i(G_n)\,p_i-\sum_{i=1}^n p_i\ge2\alpha n\Big]=1-o(1).\qquad(2)$$
--
--   Then $M$ satisfies probabilistic do no harm with respect to $\mathfrak D$. If in addition there are $\mathcal D\in\mathfrak D$ and $\alpha\in(0,1)$ with
--
--   $$\mathbb P_{\mathcal D,M,n}\Big[\sum_{i=1}^n p_i+\alpha n\le n/2\le\sum_{i=1}^n\mathrm{weight}_i(G_n)\,p_i-\alpha n\Big]=1-o(1),\qquad(3)$$
--
--   then $M$ also satisfies probabilistic positive gain with respect to $\mathfrak D$.
--
--   Here $p_i$ are the competencies of the instance. The lemma turns both properties into statements about the expected numbers of correct votes and the largest weight, which is how every model of the paper is analysed.
--
--   **Formalization Note** The standing assumptions of p. 10 are hypotheses: every $\mathcal D\in\mathfrak D$ is a probability measure giving $[0,1]^c$ measure $0$; $q$ maps $[0,1]$ into $[0,1]$ and $\varphi\ge0$ on $[0,1]^2$ (the page's typing of $q$ and $\varphi$). Measurability of $q$ and $\varphi$ (as functions on $\mathbb R$, $\mathbb R^2$) is the implicit condition behind "induce a probability measure" on p. 10. "$=1-o(1)$" is convergence of the probability to $1$; $C(n)\in o(n)$ is little-o of $n$. "$n$ a number of persons" is the limit variable.
-- source:
--   Berinsky et al., Tracking Truth with Liquid Democracy, arXiv:2107.11868v3, p. 11, Lemma 1, (1)–(3)

import Mathlib
import Definitions.Def_LiquidDemocracy_Upward_Setting

namespace LiquidDemocracy.Upward

open MeasureTheory Filter Topology Asymptotics

/-- Lemma 1, p. 11 (core lemma). Standing assumption (p. 10): every distribution of the class is a
probability measure with support in `[0,1]`; the model is typed as on p. 10 (`q : [0,1] → [0,1]`,
`φ : [0,1]² → ℝ≥0`) and measurable, so that `ℙ_{𝒟,M,n}` is a probability measure. If every `𝒟 ∈ 𝔇`
satisfies (1) and (2), then `M` satisfies probabilistic do no harm; if in addition some `𝒟 ∈ 𝔇`
satisfies (3), then `M` satisfies probabilistic positive gain. -/
theorem lemma_1 (M : Model) (𝔇 : Set (Measure ℝ))
    (h𝔇 : ∀ D ∈ 𝔇, IsProbabilityMeasure D ∧ D (Set.Icc 0 1)ᶜ = 0)
    (hq : ∀ x ∈ Set.Icc (0 : ℝ) 1, M.q x ∈ Set.Icc (0 : ℝ) 1)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, 0 ≤ M.φ x y)
    (hqm : Measurable M.q) (hφm : Measurable (Function.uncurry M.φ))
    (h12 : ∀ D ∈ 𝔇, ∃ α ∈ Set.Ioo (0 : ℝ) 1, ∃ C : ℕ → ℕ,
      (fun n => (C n : ℝ)) =o[atTop] (fun n => (n : ℝ)) ∧
      Tendsto (fun n => (instanceLaw D M n).real {ω | maxWeight ω.2 ≤ C n}) atTop (𝓝 1) ∧
      Tendsto (fun n => (instanceLaw D M n).real
        {ω | 2 * α * n ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - ∑ i, ω.1 i}) atTop (𝓝 1)) :
    ProbDNH M 𝔇 ∧
      ((∃ D ∈ 𝔇, ∃ α ∈ Set.Ioo (0 : ℝ) 1, Tendsto (fun n => (instanceLaw D M n).real
          {ω | ∑ i, ω.1 i + α * n ≤ (n : ℝ) / 2 ∧
            (n : ℝ) / 2 ≤ ∑ i, (weight ω.2 i : ℝ) * ω.1 i - α * n}) atTop (𝓝 1)) →
        ProbPG M 𝔇) := by sorry

end LiquidDemocracy.Upward
