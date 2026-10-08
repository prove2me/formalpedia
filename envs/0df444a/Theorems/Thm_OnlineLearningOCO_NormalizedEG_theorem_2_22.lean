-- Prove2me | Theorems.Thm_OnlineLearningOCO_NormalizedEG_theorem_2_22
-- name    : OnlineLearningOCO.NormalizedEG.theorem_2_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:28.708992+00:00
-- url     : https://prove2.me/theorems/255d326b-92e7-4649-aaea-83b9e149d30a
-- title:
--   Theorem 2.22 — normalized EG has regret at most log(d)/η + η Σₜ Σᵢ wₜ[i]zₜ[i]² when ηzₜ[i] ≥ −1
-- statement:
--   Let $d \ge 1$ and $\eta > 0$. The **normalized Exponentiated Gradient** algorithm on linear losses $f_t(w) = \langle w, z_t\rangle$, $z_t \in \mathbb R^d$, starts from $w_1 = (1/d, \dots, 1/d)$ and updates $w_{t+1}[i] = w_t[i] e^{-\eta z_t[i]} / \sum_j w_t[j] e^{-\eta z_t[j]}$; equivalently
--   $$w_t[i] = \frac{e^{-\eta z_{1:t-1}[i]}}{\sum_j e^{-\eta z_{1:t-1}[j]}}, \qquad z_{1:t-1} = \sum_{s=1}^{t-1} z_s .$$
--   Assume $\eta z_t[i] \ge -1$ for all $t$ and $i$. Then for every $T$ and every $u$ in the probability simplex $S = \{u \in \mathbb R^d : u \ge 0,\ \sum_i u[i] = 1\}$,
--   $$\sum_{t=1}^T \langle w_t - u, z_t\rangle \le \frac{\log d}{\eta} + \eta \sum_{t=1}^T \sum_{i=1}^d w_t[i]\, z_t[i]^2 .$$
--
--   This is the local-norm refinement of the regret bound of normalized EG: the usual term $\eta\sum_t\|z_t\|_\infty^2$ is replaced by $\eta\sum_t \|z_t\|_t^2$ with the local norm $\|z\|_t^2 = \sum_i w_t[i] z[i]^2 \le \|z\|_\infty^2$. Losses may be negative, down to $-1/\eta$. It is the tool behind the analyses of Hedge-type algorithms in the later sections of the survey.
--
--   **Formalization Note** $\log$ is the natural logarithm. The page leaves the comparator $u$ unquantified; it ranges over the probability simplex, the competing set of the normalized-entropy regularizer (the bound is false for $u$ outside it). Rounds are numbered from $0$: `wmWeights η z t` (the published weighted-majority weights, which put no restriction on the sign of the losses) is the paper's $w_{t+1}$, so `wmWeights η z 0` is the uniform vector $w_1$, and the sums run over $t \in \{0, \dots, T-1\}$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 153, Theorem 2.22 (algorithm: p. 144, normalized-EG box; p. 143, (2.10))

import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.NormalizedEG

open UnderstandingML

/-- Theorem 2.22, p. 153. Run normalized EG (box on p. 144; closed form (2.10), p. 143) with
parameter `η > 0` on linear losses `f_t(w) = ⟨w, z_t⟩` with `η z_t[i] ≥ −1` for all `t, i`. Then
for every `u` in the probability simplex of `ℝ^d`,
`∑_{t=1}^T ⟨w_t − u, z_t⟩ ≤ log(d)/η + η ∑_{t=1}^T ∑_i w_t[i] z_t[i]²`.
Rounds are 0-based: `wmWeights η z t` is the paper's `w_{t+1}` (`wmWeights η z 0` is uniform). -/
theorem theorem_2_22 {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, -1 ≤ η * z t i) (u : Fin d → ℝ) (hu0 : ∀ i, 0 ≤ u i) (hu1 : ∑ i, u i = 1)
    (T : ℕ) :
    ∑ t ∈ Finset.range T, ∑ i, (wmWeights η z t i - u i) * z t i ≤
      Real.log d / η + η * ∑ t ∈ Finset.range T, ∑ i, wmWeights η z t i * z t i ^ 2 := by sorry

end OnlineLearningOCO.NormalizedEG
