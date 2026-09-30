-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_concave
-- name    : KellyStochasticNetworks.alpha_fair_concave
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:48:58.900295+00:00
-- url     : https://prove2.me/theorems/200f79ea-ad1f-4e76-bf97-74cbfdb1cc99
-- title:
--   Exercise 8.3 — the $\alpha$-fair objective is strictly concave
-- statement:
--   For every $\alpha \in (0,\infty)$, positive weights $w_r$ and positive flow counts $n_r$, the
--   weighted $\alpha$-fair objective
--   $$G(X) = \sum_r w_r n_r^{\alpha}\frac{X_r^{1-\alpha}}{1-\alpha}
--     \qquad\Bigl(\sum_r w_r n_r \log X_r \text{ when } \alpha = 1\Bigr)$$
--   is **strictly concave** on the open positive orthant.
--
--   Three regimes have to be checked and they look different: for $0 < \alpha < 1$ the exponent
--   $1-\alpha$ is positive and the prefactor $1/(1-\alpha)$ is positive, so each summand is a
--   concave power; for $\alpha > 1$ both the exponent and the prefactor change sign, and the summand is
--   again concave; and at $\alpha = 1$ the summand is a logarithm. Strict concavity holds throughout,
--   which is what makes the $\alpha$-fair allocation unique.
--
--   Together with compactness of the feasible region this gives existence and uniqueness of the
--   allocation, so that "the $\alpha$-fair rate allocation" names a single vector — and, since the
--   problem generalizes $\mathrm{network}(A,C;w)$ of section 7.1, it is the same fact that made the
--   proportionally fair allocation well defined there.
--
--   **Formalization Note** Strict concavity is asserted on the open positive orthant, a convex set,
--   which is where real powers and the logarithm are meaningful. The book restricts attention to the
--   coordinates with $n_r > 0$; here every $n_r$ is assumed positive, which is the same restriction
--   applied to the whole index set.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 188-189 (PDF pp. 196-197): 'For all alpha in (0, infinity) and all n, the objective function is a strictly concave function of (x_r : r in R, n_r > 0); the problem is a generalization of network(A,C; w), from Section 7.1.' And Exercise 8.3: 'Check that the objective function of the problem (8.1) is concave for each of the three cases 0 < alpha < 1, alpha = 1 and 1 < alpha < infinity.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_concave {R : ℕ} (w n : Fin R → ℝ) (α : ℝ) (hα : 0 < α)
    (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r) :
    StrictConcaveOn ℝ {X : Fin R → ℝ | ∀ r, 0 < X r} (alphaFairObjective w n α) := by sorry

end KellyStochasticNetworks
