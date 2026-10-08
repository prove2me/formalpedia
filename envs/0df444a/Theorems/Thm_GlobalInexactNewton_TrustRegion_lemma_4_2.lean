-- Prove2me | Theorems.Thm_GlobalInexactNewton_TrustRegion_lemma_4_2
-- name    : GlobalInexactNewton.TrustRegion.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:23:52.201552+00:00
-- url     : https://prove2.me/theorems/a3a2e6e0-5fac-465b-9d64-c17554be4b46
-- title:
--   Lemma 4.2 — near a point where F′ is invertible, every model minimizer satisfies ‖s‖ ≤ Γ·pred(s)
-- statement:
--   Let $E$ be a finite-dimensional real space with an arbitrary norm, and let $F:E\to E$ be continuously differentiable. If $x_*$ is such that $F'(x_*)$ is invertible, then there exist $\Gamma>0$ and $\epsilon_*>0$ such that, for any $\delta>0$, every
--   $$s\in\arg\min_{\|\bar s\|\le\delta}\|F(x)+F'(x)\,\bar s\|\tag{4.5}$$
--   satisfies
--   $$\|s\|\le\Gamma\bigl\{\|F(x)\|-\|F(x)+F'(x)\,s\|\bigr\}\tag{4.6}$$
--   whenever $\|x-x_*\|<\epsilon_*$.
--
--   Combined with Lemma 4.1, this gives the second half of Theorem 4.4: near a limit point with invertible derivative, trust region steps are controlled by their predicted reduction, uniformly in the radius.
--
--   **Formalization Note.** The paper says "there exist $\Gamma$ and $\epsilon_*>0$"; we read both as positive (the proof gives $\Gamma=2\|F'(x_*)^{-1}\|$, and any larger $\Gamma$ also works), which is the stronger reading. "$F'(x_*)$ is invertible" is `(fderiv ℝ F xstar).IsInvertible`, i.e. $F'(x_*)$ is a continuous linear automorphism of $E$. The statement holds for every minimizer, since the minimizer need not be unique for a general norm.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 404, Lemma 4.2, (4.5), (4.6)

import Mathlib
import Definitions.Def_GlobalInexactNewton_TrustRegion_Method

namespace GlobalInexactNewton.TrustRegion

open Filter Topology

/-- Lemma 4.2, p. 404. -/
theorem lemma_4_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (xstar : E) (hinv : (fderiv ℝ F xstar).IsInvertible) :
    ∃ Γ > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ δ : ℝ, 0 < δ → ∀ x ∈ Metric.ball xstar ε, ∀ s : E,
      IsLinModelMin F x δ s → ‖s‖ ≤ Γ * (‖F x‖ - ‖F x + fderiv ℝ F x s‖) := by sorry

end GlobalInexactNewton.TrustRegion
