-- Prove2me | Theorems.Thm_ModernOnlineLearning_LowerBounds_theorem_5_4
-- name    : ModernOnlineLearning.LowerBounds.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:11.820987+00:00
-- url     : https://prove2.me/theorems/083ca68f-5e9f-482b-9be2-e1e750b550a8
-- title:
--   Theorem 5.4 — unprojected OSD with t^(−α) steps can incur order T^(2−α) regret
-- statement:
--   Fix a Euclidean dimension $d\ge1$, $0<\alpha<1$, and define $\phi(\alpha)$ as above. If the horizon satisfies $T\ge2/((1-\alpha)\phi(\alpha))$, then there is a sequence of convex, $1$-Lipschitz losses for which unprojected online subgradient descent, initialized at $x_1=0$ and using step size $t^{-\alpha}$, has
--
--   $$
--   \operatorname{Regret}_T(0)\ge\tfrac12\phi(\alpha)T^{2-\alpha}.
--   $$
--
--   This shows that the same decaying steps can perform much worse when there is no bounded feasible domain.
--
--   **Formalization Note** The losses are represented by linear functions $z\mapsto\langle g_t,z\rangle$ with $\|g_t\|_2\le1$, as in the book's construction. Their convexity and Lipschitz property follow from this form. The displayed limit $\lim_{\alpha\to1}\phi(\alpha)=1-\ln2$ is a separate claim and is outside this item.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 5.4 and its construction, p. 52

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_phi

namespace ModernOnlineLearning.LowerBounds

/-- The existence and regret-bound part of Theorem 5.4, printed p. 52.
The adversarial losses are linear along one coordinate, as in the source proof;
the limit statement about `φ` is not part of this declaration. -/
theorem theorem_5_4 {d : ℕ} (hd : 0 < d)
    (α : ℝ) (hαpos : 0 < α) (hαlt : α < 1)
    (T : ℕ) (hT : 2 / ((1 - α) * phi α) ≤ (T : ℝ)) :
    ∃ (g x : ℕ → EuclideanSpace ℝ (Fin d)),
      x 1 = 0 ∧
      (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ 1) ∧
      (∀ t ∈ Finset.Icc 1 T,
        x (t + 1) = x t - ((t : ℝ) ^ (-α)) • g t) ∧
      (1 / 2 : ℝ) * phi α * (T : ℝ) ^ (2 - α) ≤
        ∑ t ∈ Finset.Icc 1 T, inner ℝ (g t) (x t) := by sorry

end ModernOnlineLearning.LowerBounds
