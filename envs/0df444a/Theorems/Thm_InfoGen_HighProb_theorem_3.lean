-- Prove2me | Theorems.Thm_InfoGen_HighProb_theorem_3
-- name    : InfoGen.HighProb.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:09.853913+00:00
-- url     : https://prove2.me/theorems/59fea93d-8cd6-4b40-b566-107c3f5c179f
-- title:
--   Theorem 3, p. 4 — if I(Λ_W(S);W) ≤ ε, then n ≥ (8σ²/α²)(ε/β + log(2/β)) gives P[|L_μ(W) − L_S(W)| > α] ≤ β (countable W)
-- statement:
--   Let $\mathsf W$ be a countable hypothesis space, $\mathsf Z$ an instance space with a probability measure $\mu$, and $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable nonnegative loss such that $\ell(w,Z)$ is $\sigma$-subgaussian under $\mu$ for all $w\in\mathsf W$:
--   $$\log\mathbb E\big[e^{\lambda(\ell(w,Z) - L_\mu(w))}\big] \le \frac{\lambda^2\sigma^2}{2}\quad\text{for all }\lambda\in\mathbb R .$$
--   Let $P_{W|S}$ be a learning algorithm that receives $S = (Z_1,\dots,Z_n)$, i.i.d. with law $\mu$, and outputs $W\in\mathsf W$. Write $L_\mu(w) = \mathbb E[\ell(w,Z)]$, $L_S(w) = \frac1n\sum_{i=1}^n \ell(w,Z_i)$, and $\Lambda_{\mathsf W}(S) = (L_S(w))_{w\in\mathsf W}$.
--
--   Suppose the algorithm satisfies $I(\Lambda_{\mathsf W}(S);W)\le\varepsilon$ for some $\varepsilon\ge0$. Then for any $\alpha>0$ and $0<\beta\le1$, every sample size $n\ge1$ with
--   $$n \ge \frac{8\sigma^2}{\alpha^2}\Big(\frac{\varepsilon}{\beta} + \log\frac{2}{\beta}\Big)$$
--   guarantees
--   $$\mathbb P\big[\,|L_\mu(W) - L_S(W)| > \alpha\,\big] \le \beta,$$
--   where the probability is taken with respect to the joint distribution $P_{S,W} = \mu^{\otimes n}\otimes P_{W|S}$.
--
--   When $W$ is independent of $S$ the Chernoff–Hoeffding bound gives the sample size $\frac{2\sigma^2}{\alpha^2}\log\frac2\beta$; the theorem shows that a sample complexity polynomial in $1/\alpha$ and logarithmic in $1/\beta$ still suffices when $W$ depends on $S$, as long as the mutual information between the empirical risks and the output is small. Any algorithm with $I(S;W)\le\varepsilon$ qualifies, since $I(\Lambda_{\mathsf W}(S);W)\le I(S;W)$.
--
--   **Formalization Note.** Three departures from the print, each disclosed. (1) The paper writes "a sample complexity of $n = \frac{8\sigma^2}{\alpha^2}(\frac{\varepsilon}{\beta} + \log\frac{2}{\beta})$"; the proof shows that the failure probability exceeding $\beta$ forces $n$ below this value, so the statement is posed for every $n$ at least this value. (2) The paper asserts its results hold "even when $\mathsf W$ is uncountably infinite" (p. 4). Under the product σ-algebra on $\mathbb R^{\mathsf W}$ this is false: with $\mathsf Z = [0,1]$, $\mu$ uniform, $\mathsf W = [0,1]^n$, $\ell(w,z) = \mathbf 1\{z\in\{w_1,\dots,w_n\}\}$ and the algorithm $W = S$, each $L_S(w)$ is $0$ almost surely, so $I(\Lambda_{\mathsf W}(S);W) = 0$, while $|L_\mu(W) - L_S(W)| = 1$ always. Hence $\mathsf W$ is countable with measurable singletons (Russo and Zou's setting). (3) $n\ge1$, $\varepsilon\ge0$ and joint measurability of $\ell$ are added: a dataset is nonempty (for $\sigma = 0$ the displayed condition alone would allow $n = 0$), a mutual information is nonnegative, and $L_\mu(W)$, $L_S(W)$ must be random variables. Mutual information is valued in $[0,\infty]$, and the probability in $[0,\infty]$ is compared with $\beta$.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Theorem 3, eqs. (15)–(16), p. 4; proof App. B, pp. 11–12

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem theorem_3 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn0 : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε : lambdaInfo ℓ μ κ ≤ ENNReal.ofReal ε)
    (α β : ℝ) (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hn : 8 * (σ : ℝ) ^ 2 / α ^ 2 * (ε / β + Real.log (2 / β)) ≤ n) :
    (sampleLaw μ n ⊗ₘ κ) {p | α < |risk ℓ μ p.2 - empRisk ℓ p.1 p.2|} ≤
      ENNReal.ofReal β := by sorry

end InfoGen.HighProb
