-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_2
-- name    : ManyServerQED.Scheduling.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:04:00.368636+00:00
-- url     : https://prove2.me/theorems/0ffab096-e41d-4dac-9a0a-dd323a8b66d3
-- title:
--   Proposition 2 — existence and pathwise uniqueness of the controlled diffusion (27)
-- statement:
--   Let $(\ell,\mu,\theta,r)$ be diffusion data and $b$ the drift (26). For every initial point $x\in\mathbb R^k$ and every admissible system $\pi=(\Omega,\mathcal F,(\mathcal F_t),P,u,W)$ there is a controlled process $X$ associated with $x$ and $\pi$: a continuous adapted process satisfying
--   $$
--   X(t)=x+rW(t)+\int_0^tb(X(s),u(s))\,ds,\qquad t\ge0,\quad P\text{-a.s.}
--   $$
--   Moreover, if $X$ and $\bar X$ are two controlled processes associated with $x$ and $\pi$, then $X(t)=\bar X(t)$ for all $t\ge0$, $P$-a.s.
--
--   Proposition 2 makes the cost $C(x,\pi)$ and the value $V$ well defined.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 17, Proposition 2

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 2 (p. 17): for every initial point `x` and admissible system `π` there is a
controlled process associated with `x` and `π`, and any two such processes agree for all `t ≥ 0`,
`P`-a.s. -/
theorem proposition_2 {k : ℕ} [NeZero k] (D : DiffusionData k) (π : AdmissibleSystem k) (x : Fin k → ℝ) :
    (∃ X : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X) ∧
      ∀ X Y : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X → IsControlledProcess D π x Y →
        ∀ᵐ ω ∂π.P, ∀ t, X t ω = Y t ω := by sorry

end ManyServerQED.Scheduling
