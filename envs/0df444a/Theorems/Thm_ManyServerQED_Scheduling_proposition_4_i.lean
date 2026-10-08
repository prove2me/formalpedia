-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_4_i
-- name    : ManyServerQED.Scheduling.proposition_4_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:04:09.303768+00:00
-- url     : https://prove2.me/theorems/143c6914-86f9-4b6e-a24c-afa9e0b8f492
-- title:
--   Proposition 4(i) — Lipschitz dependence of the controlled diffusion on its initial point
-- statement:
--   Let $(\ell,\mu,\theta,r)$ be diffusion data. There is a constant $c$, depending only on these data, with the following property. For every admissible system $\pi$, all $x,\bar x\in\mathbb R^k$, and controlled processes $X$ (for $x$ and $\pi$) and $\bar X$ (for $\bar x$ and the same $\pi$),
--   $$
--   \|X_t-\bar X_t\|\le\|x-\bar x\|\,(1+e^{ct}),\qquad t\ge0,\quad P\text{-a.s.}
--   $$
--   Here $\|\cdot\|$ is the $\ell^1$ norm.
--
--   This estimate is the input to the continuity of the value function (Proposition 5(ii)).
--
--   **Formalization Note** The paper writes $|X_t-\bar X_t|$ and $|x-\bar x|$ for vectors; we read $|\cdot|$ as the paper's norm $\|\cdot\|$. The constant is quantified before the system, the initial points and the time.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 23, Proposition 4(i)

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 4(i) (p. 23): there is a constant `c`, depending only on the diffusion data, such that
for every admissible system `π` and controlled processes `X`, `X̄` associated with `(x, π)` and
`(x̄, π)`, `P`-a.s. `‖X_t − X̄_t‖ ≤ ‖x − x̄‖(1 + e^{ct})` for all `t ≥ 0` (ℓ¹ norm). -/
theorem proposition_4_i {k : ℕ} [NeZero k] (D : DiffusionData k) :
    ∃ c : ℝ, ∀ (π : AdmissibleSystem k) (x xbar : Fin k → ℝ) (X Xbar : ℝ≥0 → π.Ω → Fin k → ℝ),
      IsControlledProcess D π x X → IsControlledProcess D π xbar Xbar →
        ∀ᵐ ω ∂π.P, ∀ t : ℝ≥0,
          l1norm (X t ω - Xbar t ω) ≤ l1norm (x - xbar) * (1 + Real.exp (c * t)) := by sorry

end ManyServerQED.Scheduling
