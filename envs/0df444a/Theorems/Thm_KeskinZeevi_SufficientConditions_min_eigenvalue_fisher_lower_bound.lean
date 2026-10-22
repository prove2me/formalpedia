-- Prove2me | Theorems.Thm_KeskinZeevi_SufficientConditions_min_eigenvalue_fisher_lower_bound
-- name    : KeskinZeevi.SufficientConditions.min_eigenvalue_fisher_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T04:00:37.992656+00:00
-- url     : https://prove2.me/theorems/9d587121-5541-4059-8f3b-d9951f87c38a
-- title:
--   Lemma 2 (corrected constant) — minimum eigenvalue of the empirical Fisher information
-- statement:
--   Let $0 \le l < u$, and let $p_1, \dots, p_t \in [l,u]$ be any prices. Write $\mathcal{J}_t = \sum_{s=1}^t \begin{bmatrix} 1 & p_s \\ p_s & p_s^2\end{bmatrix}$ for the empirical Fisher information, $\mu_{\min}(t)$ for its smallest eigenvalue, and $J_t = \sum_{s=1}^t (p_s - \bar p_t)^2$ for the information metric. Then
--   $$\mu_{\min}(t) \;\ge\; \gamma' J_t, \qquad \gamma' = \frac{1}{1 + u^2 + (u-l)^2}.$$
--
--   The lemma is deterministic and holds for every $t$ and every price sequence. It converts the scalar $J_t$ into a lower bound on the curvature of the least squares problem in every direction. That is how the growth of $J_t$ controls the estimation error in Lemma 3.
--
--   **Formalization Note.** This is a **correction** of the printed statement. The paper claims the constant $\gamma = 2/(1+2u-l)^2$, which is false. For $l = 9.9$, $u = 10$, $t = 2$, $p_1 = 9.9$, $p_2 = 10$ one gets $\mu_{\min}(2) \approx 5.0\cdot 10^{-5} < \gamma J_2 \approx 8.1 \cdot 10^{-5}$. A sorry-free Lean proof of this counterexample exists outside the mission. The corrected constant $\gamma'$ plays the same role, and the downstream arguments use only $\gamma' > 0$. The smallest eigenvalue is written as `minRayleigh`, the infimum of $y^{\mathsf T}\mathcal{J}_t y$ over Euclidean unit vectors $y$. The hypothesis $0 \le l$ is the paper's standing assumption on prices.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1147, Lemma 2 (constant corrected; see Formalization Note)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares

namespace KeskinZeevi.SufficientConditions

/-- Keskin–Zeevi 2014, p. 1147, Lemma 2, with a corrected constant: for any prices
`p_1, …, p_t ∈ [l, u]` with `0 ≤ l < u`, the smallest eigenvalue of the empirical Fisher
information `𝒥_t` is at least `γ' J_t` with `γ' = 1 / (1 + u² + (u - l)²)`. (The printed
`γ = 2 / (1 + 2u - l)²` is false, e.g. `l = 9.9`, `u = 10`, `p = (9.9, 10)`.) -/
theorem min_eigenvalue_fisher_lower_bound (l u : ℝ) (hl : 0 ≤ l) (hlu : l < u)
    (p : ℕ → ℝ) (t : ℕ) (hp : ∀ s ∈ Finset.Icc 1 t, p s ∈ Set.Icc l u) :
    (1 / (1 + u ^ 2 + (u - l) ^ 2)) * infoMetricOf p t ≤ minRayleigh (fisherOf p t) := by sorry

end KeskinZeevi.SufficientConditions
