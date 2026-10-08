-- Prove2me | Theorems.Thm_GlobalInexactNewton_TrustRegion_lemma_4_3
-- name    : GlobalInexactNewton.TrustRegion.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:24.411325+00:00
-- url     : https://prove2.me/theorems/f6baa721-6624-4ea2-8a01-837a017a4e1a
-- title:
--   Lemma 4.3 — near a non-stationary point of ‖F‖, model minimizers over small radii satisfy ‖s‖ ≤ Γ·pred(s)
-- statement:
--   Let $E$ be a finite-dimensional real space with an arbitrary norm, and let $F:E\to E$ be continuously differentiable. If $x_*$ is not a stationary point of $\|F\|$, i.e. $\|F(x_*)\|>\|F(x_*)+F'(x_*)s\|$ for some $s$, then there exist $\Gamma>0$, $\delta_*>0$ and $\epsilon_*>0$ such that every
--   $$s\in\arg\min_{\|\bar s\|\le\delta}\|F(x)+F'(x)\,\bar s\|\tag{4.5}$$
--   satisfies
--   $$\|s\|\le\Gamma\bigl\{\|F(x)\|-\|F(x)+F'(x)\,s\|\bigr\}\tag{4.6}$$
--   whenever $\|x-x_*\|<\epsilon_*$ and $0<\delta\le\delta_*$.
--
--   Combined with Lemma 4.1, this is what rules out non-stationary limit points of Algorithm TR in Theorem 4.4.
--
--   **Formalization Note.** "There exist $\Gamma$, $\delta_*>0$, and $\epsilon_*>0$" is read with $\Gamma>0$ as well (the proof gives $\Gamma=2\|s_*\|/[(1-\eta_*)\|F(x_*)\|]>0$), which is the stronger reading. The constants $\Gamma,\delta_*,\epsilon_*$ are chosen before $x$ and $\delta$, as in the paper. The statement holds for every minimizer.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 404, Lemma 4.3

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

/-- Lemma 4.3, p. 404. -/
theorem lemma_4_3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (xstar : E) (hns : ¬ IsStationaryPtNorm F xstar) :
    ∃ Γ > (0 : ℝ), ∃ δstar > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ x ∈ Metric.ball xstar ε, ∀ δ : ℝ,
      0 < δ → δ ≤ δstar → ∀ s : E,
        IsLinModelMin F x δ s → ‖s‖ ≤ Γ * (‖F x‖ - ‖F x + fderiv ℝ F x s‖) := by sorry

end GlobalInexactNewton.TrustRegion
