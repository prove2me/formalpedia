-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_lemma_8_1
-- name    : GaussMixGated.ExactReal.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:19.249391+00:00
-- url     : https://prove2.me/theorems/f86b4cd8-cc7e-477a-960b-065525b5907a
-- title:
--   Lemma 8.1 — Filter guarantee (corrected: non-strict at B = 0)
-- statement:
--   Fix $\alpha=1/100$. Let $n\ge1$, $x_1,\dots,x_n\in\mathbb R^d$, $K>0$, $B\ge0$, and suppose an unknown set $G_0$ with $|G_0|\ge(1-\alpha)n$ satisfies (50) for an unknown mean $m$:
--
--   $$\frac1n\sum_{i\in G_0}(x_i-m)(x_i-m)^{\top}\preceq KB^2I_d.$$
--
--   Run the filter of §8.3 with any direction rule that returns, for every nonzero PSD $M$, a unit $v$ with $\lambda_{\max}(M)/2\le v^{\top}Mv\le\lambda_{\max}(M)$. The returned point $a$ satisfies
--
--   $$\|a-m\|\le3\sqrt KB,\qquad\text{and}\qquad\|a-m\|<3\sqrt KB\ \text{ when }B>0.$$
--
--   The filter turns the regular subset of (49)–(50) into a mean estimate with dimension-free error, which is what keeps the posterior cover's radius independent of $d$.
--
--   Differences from the source:
--   - generalization: 'the finite spectral procedure below' chooses v → any direction rule meeting the step-2 inequality; reason: the spectral step of PDF p. 22 meets it, so the statement specializes to the source's filter
--   - correction: strict bound ‖a − m‖ < 3√K B for the known nonnegative scale B → ‖a − m‖ ≤ 3√K B for B ≥ 0, with the strict bound retained for B > 0; reason: the printed strict bound fails for n = d = 1, x₁ = m = 0, G₀ = {1}, K = 1, B = 0: (50) holds, the filter returns 0, and 0 < 0 is false; the proof gives the non-strict bound at zero
--   - encoding: Repeat at most n times → a recursion with fuel n; reason: same algorithm; g_max as a fold of max over the positive-weight scores, which are nonnegative
--   - generalization: the ambient dimension d ≥ 1 of the mixture setting → also d = 0 for the deterministic filter guarantee; reason: in dimension zero every vector and the filter output are zero; the positive-scale strict bound is still true, and every source dimension is included
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 21 (printed p. 19), Lemma 8.1; filter on PDF pp. 20–21

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Filter

namespace GaussMixGated.ExactReal

/-- Lemma 8.1 (Filter guarantee) (Zheng–Xie–He, STOC 2027 #36, PDF p. 21): with `α = 1/100`, if
`x_1, …, x_n` contain a set `G₀` with `|G₀| ≥ (1 − α)n` satisfying (50) for a mean `m` and scale
`B`, the filter of §8.3 (run with any direction rule meeting the step-2 inequality) returns `a`
with `‖a − m‖ ≤ 3√K B`, and `‖a − m‖ < 3√K B` when `B > 0`.

Source correction at `B = 0`: take `n = d = 1`, `x₁ = m = 0`, `G₀ = {1}` and `K = 1`.
The hypothesis (50) holds and the filter returns `0`, so the printed strict bound would be
`0 < 0`. The non-strict bound covers this boundary; the strict positive-scale claim is kept. -/
theorem lemma_8_1 {n d : ℕ} (hn : 1 ≤ n) (x : Fin n → EuclideanSpace ℝ (Fin d)) (K B : ℝ)
    (hK : 0 < K) (hB : 0 ≤ B)
    (choose : Matrix (Fin d) (Fin d) ℝ → EuclideanSpace ℝ (Fin d))
    (hchoose : IsDirectionRule choose) (m : EuclideanSpace ℝ (Fin d)) (G₀ : Finset (Fin n))
    (hG₀ : (1 - 1 / 100 : ℝ) * n ≤ G₀.card)
    (h50 : ∀ v : EuclideanSpace ℝ (Fin d),
      (1 / (n : ℝ)) * ∑ i ∈ G₀, dotE v (x i - m) ^ 2 ≤ K * B ^ 2 * ‖v‖ ^ 2) :
    ‖robustFilter x K B choose - m‖ ≤ 3 * Real.sqrt K * B ∧
    (0 < B → ‖robustFilter x K B choose - m‖ < 3 * Real.sqrt K * B) := by sorry

end GaussMixGated.ExactReal
