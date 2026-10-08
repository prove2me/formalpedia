-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_proposition_2_2
-- name    : KleywegtSAA.ExpRate.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:45.123979+00:00
-- url     : https://prove2.me/theorems/669eb0f6-f250-40c6-b7c4-94e5ad77d9db
-- title:
--   Proposition 2.2, (2.5), p. 4 — under Assumption A, ∃ γ > 0: limsup (1/N) log[1 − P(Ŝ^ε_N ⊂ 𝒮^ε)] ≤ −γ
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $G : \mathcal S \times \mathcal W \to \mathbb R$, and $W^1, W^2, \dots$ an i.i.d. sample of the random vector $W$ such that $G(x, \cdot)$ is measurable and $\mathbb E|G(x,W)| < \infty$ for every $x \in \mathcal S$. Let $g(x) = \mathbb E\, G(x,W)$ and $\hat g_N(x) = N^{-1}\sum_{n=1}^N G(x, W^n)$, and let $\mathcal S^\varepsilon$ and $\hat{\mathcal S}^\varepsilon_N$ be the sets of $\varepsilon$-optimal solutions of $\min_{\mathcal S} g$ and $\min_{\mathcal S} \hat g_N$.
--
--   Suppose Assumption A holds: for every $x \in \mathcal S$ the moment generating function of $G(x,W)$ is finite in a neighbourhood of $0$. Then for every $\varepsilon \ge 0$ there is a constant $\gamma > 0$ such that
--   $$\limsup_{N \to \infty} \frac1N \log\Big[1 - P\big(\hat{\mathcal S}^\varepsilon_N \subset \mathcal S^\varepsilon\big)\Big] \le -\gamma.$$
--
--   That is, the probability that every $\varepsilon$-optimal solution of the sample average approximation is an $\varepsilon$-optimal solution of the true problem tends to one exponentially fast in the sample size.
--
--   **Formalization Note** The standing setting of §1–§2 is carried as hypotheses: $\mathcal S$ is a nonempty finite set of an arbitrary type, each $G(x,\cdot)$ is measurable, the sample $W^1, W^2, \dots$ is an independent, identically distributed sequence of measurable maps on a probability space $(\Omega, P)$ (the paper's $W^n$ is the $(n-1)$-st term of a $0$-indexed sequence, and the law of $W$ is that of the first term), and $E|G(x,W)| < \infty$ for every $x \in \mathcal S$. The logarithm is `ENNReal.log` with $\log 0 = -\infty$ and the limit superior is taken in the extended reals, so the statement remains correct (with value $-\infty$) when the event is sure, e.g. when $\mathcal S^\varepsilon = \mathcal S$. The constant $\gamma$ may depend on $\varepsilon$, as on the page, where it depends on $\alpha(\varepsilon)$. The term at $N = 0$ is $0$ and does not affect the limit superior.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 4, Proposition 2.2 and (2.5)

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- Proposition 2.2 and (2.5), p. 4: under Assumption A, for every `ε ≥ 0` there is `γ > 0` with
`limsup_{N → ∞} (1/N) log[1 − P(Ŝ^ε_N ⊂ S^ε)] ≤ −γ` (with `log 0 = −∞`). -/
theorem proposition_2_2
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hA : AssumptionA S G P W) :
    ∀ ε : ℝ, 0 ≤ ε → ∃ γ : ℝ, 0 < γ ∧
      Filter.limsup (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : EReal) *
          ENNReal.log (1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆
            epsSet S hS (trueObj G P W) ε})) atTop ≤ ((-γ : ℝ) : EReal) := by sorry

end KleywegtSAA.ExpRate
