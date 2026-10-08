-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_deviation_le_two_exp
-- name    : KleywegtSAA.ExpRate.deviation_le_two_exp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:10.953993+00:00
-- url     : https://prove2.me/theorems/922fcd81-2c1f-42fc-81f7-40d12f330b14
-- title:
--   §2.2, p. 4 — under Assumption A, P{|ĝ_N(x) − g(x)| ≥ α(ε)/2} ≤ e^{−Nγ_x} + e^{−Nγ′_x}
-- statement:
--   Assume the standing setting of §1–§2 and Assumption A. Let $r > 0$. Then for every $x \in \mathcal S$ there are constants $\gamma_x > 0$ and $\gamma'_x > 0$ such that for every sample size $N \ge 1$,
--   $$P\big\{ |\hat g_N(x) - g(x)| \ge r \big\} \le e^{-N\gamma_x} + e^{-N\gamma'_x}.$$
--
--   On the page $r = \alpha(\varepsilon)/2$, and $\gamma_x, \gamma'_x$ are the values of the rate functions of $G(x,W)$ and $-G(x,W)$ at $g(x) + r$ and $-g(x) + r$. Taking $\gamma = \min_{x \in \mathcal S}\{\gamma_x, \gamma'_x\}$ and summing over $\mathcal S$ in the union bound yields Proposition 2.2.
--
--   **Formalization Note** The standing setting of §1–§2 is carried as hypotheses: $\mathcal S$ is a nonempty finite set of an arbitrary type, each $G(x,\cdot)$ is measurable, the sample $W^1, W^2, \dots$ is an independent, identically distributed sequence of measurable maps on a probability space $(\Omega, P)$ (the paper's $W^n$ is the $(n-1)$-st term of a $0$-indexed sequence, and the law of $W$ is that of the first term), and $E|G(x,W)| < \infty$ for every $x \in \mathcal S$. The statement is made for every $r > 0$ rather than only for $r = \alpha(\varepsilon)/2$; this is stronger and avoids the nonemptiness of $\mathcal S \setminus \mathcal S^\varepsilon$. The constants are real numbers: when a rate function is $+\infty$, any positive constant works.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 4, §2.2, after Assumption A

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- §2.2, p. 4: under Assumption A, for every `r > 0` (the page's `r = α(ε)/2`) and every
`x ∈ S` there are `γ_x, γ'_x > 0` with `P{|ĝ_N(x) − g(x)| ≥ r} ≤ e^{−Nγ_x} + e^{−Nγ'_x}` for all
`N ≥ 1`. -/
theorem deviation_le_two_exp
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hA : AssumptionA S G P W) (r : ℝ) (hr : 0 < r) :
    ∀ x ∈ S, ∃ γx γx' : ℝ, 0 < γx ∧ 0 < γx' ∧ ∀ N : ℕ, 1 ≤ N →
      P {ω | r ≤ |sampleObj G W N ω x - trueObj G P W x|} ≤
        ENNReal.ofReal (Real.exp (-((N : ℝ) * γx)) + Real.exp (-((N : ℝ) * γx'))) := by sorry

end KleywegtSAA.ExpRate
