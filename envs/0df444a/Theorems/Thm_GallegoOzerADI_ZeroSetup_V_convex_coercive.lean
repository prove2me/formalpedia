-- Prove2me | Theorems.Thm_GallegoOzerADI_ZeroSetup_V_convex_coercive
-- name    : GallegoOzerADI.ZeroSetup.V_convex_coercive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:54:13.048144+00:00
-- url     : https://prove2.me/theorems/3bf234be-c810-43b7-aad9-743c682a68cc
-- title:
--   Theorem 4, Part 1 — $V_t(\cdot, o_t)$ is convex and tends to $\infty$ as $|x| \to \infty$
-- statement:
--   Consider the inventory model with advance demand information and zero set-up cost under its standing hypotheses: information horizon $N > L + 1$, convex and coercive single-period costs $G_t$ of at most linear growth, discount factors $\alpha_{t+1} > 0$, and nonnegative demand vectors $D_t$ with finite means. Let $V_t$ be defined by the functional equation
--
--   $$J_t(x, o) = \inf_{y \ge x} V_t(y, o), \qquad V_t(y, o) = G_t(y) + \alpha_{t+1}\, \mathbb{E}\, J_{t+1}(x_{t+1}, o_{t+1}), \qquad J_{T+1} \equiv 0.$$
--
--   Then for every period $t \in \{1, \dots, T\}$ and every fixed vector $o_t \in \mathbb{R}^{N-L-1}$ of observed demands,
--
--   $$x \mapsto V_t(x, o_t) \text{ is convex} \qquad\text{and}\qquad \lim_{|x| \to \infty} V_t(x, o_t) = \infty.$$
--
--   This is the base of the analysis of the zero set-up cost case: it guarantees that $V_t(\cdot, o_t)$ has a smallest minimizer, the base-stock level.
--
--   **Formalization Note.** The limit is expressed as convergence to $+\infty$ along the cocompact filter of $\mathbb{R}$. No sign condition on $o_t$ is imposed, as in the paper. The standing hypotheses the paper uses without stating (coercivity of $G_t$ rather than of $\tilde G_t$, nonnegative demand, positive discount factors, finiteness of the expectation) are part of `Model.Assumptions`.
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Theorem 4, Part 1

import Mathlib
import Definitions.Def_GallegoOzerADI_ZeroSetup_Model

open MeasureTheory Filter Topology

namespace GallegoOzerADI.ZeroSetup

/-- Theorem 4, Part 1 (p. 1351): for every period `t ∈ {1, …, T}` and every fixed vector `o_t`,
`V_t(·, o_t)` is convex and `V_t(x, o_t) → ∞` as `|x| → ∞`. -/
theorem V_convex_coercive {L M : ℕ} (P : Model L M) (hP : P.Assumptions)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) (o : Fin M → ℝ) :
    ConvexOn ℝ Set.univ (fun x => P.V t x o) ∧
      Tendsto (fun x => P.V t x o) (cocompact ℝ) atTop := by sorry

end GallegoOzerADI.ZeroSetup
