-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_proposition_2_existence
-- name    : ManyServerQED.Scheduling.proposition_2_existence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-07T05:09:16.240938+00:00
-- url     : https://prove2.me/theorems/2a38d9f2-63c5-4033-8e77-fbefd9ddfa4e
-- title:
--   Proposition 2 (existence part), p. 17 — a controlled process exists
-- statement:
--   Let $(\ell,\mu,\theta,r)$ be diffusion data and $b(x,u)=\ell+(\mu-\theta)(\mathbb 1\cdot x)^+u-\mu x$ the drift (26). For every initial point $x\in\mathbb R^k$ and every admissible system $\pi=(\Omega,\mathcal F,(\mathcal F_t),P,u,W)$ there exists a controlled process $X$ associated with $x$ and $\pi$: a process with continuous paths, adapted to $(\mathcal F_t)$, with $\int_0^t|b(X(s),u(s))|\,ds<\infty$ for all $t$ a.s., and
--   $$
--   X(t)=x+rW(t)+\int_0^t b(X(s),u(s))\,ds,\qquad 0\le t<\infty,\quad P\text{-a.s.}\qquad(27)
--   $$
--
--   This is the existence half of Proposition 2 (a strong solution of (27) exists). The uniqueness half follows from Proposition 4(i).
--
--   **Formalization note.** The objects are exactly those of the milestone `proposition_2`: `IsControlledProcess` requires every path to be continuous and $X(t)$ to be $\mathcal F_t$-measurable, and (27) to hold almost surely.
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 17, Proposition 2 (existence); proof in Appendix A.1, p. 43

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Proposition 2 (p. 17), existence part (proof in Appendix A.1, p. 43): for every initial point
`x` and admissible system `π` there is a controlled process associated with `x` and `π`
(a strong solution of (27)). -/
theorem proposition_2_existence {k : ℕ} [NeZero k] (D : DiffusionData k) (π : AdmissibleSystem k)
    (x : Fin k → ℝ) :
    ∃ X : ℝ≥0 → π.Ω → Fin k → ℝ, IsControlledProcess D π x X := by sorry

end ManyServerQED.Scheduling
