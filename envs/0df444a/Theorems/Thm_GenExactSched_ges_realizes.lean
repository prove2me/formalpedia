-- Prove2me | Theorems.Thm_GenExactSched_ges_realizes
-- name    : GenExactSched.ges_realizes
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:56.341284+00:00
-- url     : https://prove2.me/theorems/d3fce962-052b-4c0c-991b-be7a7b3b237a
-- title:
--   Appendix E — Generalized Exact Scheduling (25) produces the rates (96) (corrected: no service after the deadline when $\delta/2\le\sqrt\varepsilon$)
-- statement:
--   Let $\delta\ge0$, $\varepsilon>0$, and let $u^*$ be Generalized Exact Scheduling (25) with its corrected third line:
--
--   $$u^*(x,y)=\begin{cases}x/y,& y>0,\ x/y\le\min\{\delta/2,\sqrt\varepsilon\},\\ \delta/2,& y>0,\ x/y>\delta/2,\ \delta/2\le\sqrt\varepsilon,\\ \sqrt\varepsilon\,\mathbf 1\{x>0\},& \delta/2>\sqrt\varepsilon\text{ and not the first case},\\ 0,& \delta/2\le\sqrt\varepsilon,\ y\le0.\end{cases}$$
--
--   For every job with $0\le\sigma\le\tau$, the remaining demand under $u^*$ has a trajectory: a continuous $x\ge0$ on $[0,\infty)$ with $x(s)=\sigma-\int_0^s u^*(x(s'),\tau-s')\,ds'$; and along **every** such trajectory the service rate at elapsed time $s$ is $v^*(\sigma,\tau,\tau-s)$ for almost every $s\ge0$, where $v^*$ is the profile (96).
--
--   So the distributed policy, which sees only a job's own remaining demand and remaining time, realizes the optimal rate profile of Lemma 9; this is the step from Lemma 9 to Theorem 4.
--
--   Differences from the source:
--   - correction: policy (25), third line "√ε 1{x > 0} otherwise" → √ε 1{x > 0} only when δ/2 > √ε (and not the first line); rate 0 when δ/2 ≤ √ε and y ≤ 0 (uStar); reason: printed (25) keeps serving past the deadline when δ/2 < √ε: σ = τ = 1, δ = ε = 1 gives cost 5/4, not the claimed optimum 3/4 (paper.md item 1).
--   - encoding: "scheduler (25) of the form (4) can produce identical service rates to (96)" → a trajectory (continuous, ≥ 0, x(s) = σ − ∫₀ˢ u(x(s'), τ − s') ds') exists, and along every trajectory the rate equals v*(σ, τ, τ − s) for a.e. s ≥ 0 (Produces); reason: the realized rate of a form (4) policy is defined through the remaining-demand trajectory; requiring it along every trajectory rules out a choice of solution.
--   - generalization: jobs with (σ, τ) ∈ S → every job with 0 ≤ σ ≤ τ, including τ = 0; reason: S ⊆ {0 ≤ σ ≤ τ}, so it specializes to every job type of the paper.
--   - encoding: unit costs δ, ε without stated signs → 0 ≤ δ and 0 < ε as hypotheses; reason: unit costs; ε > 0 as in the goal (paper.md item 7).
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, Appendix E, last paragraph, p. 43 (policy (25), p. 13; profile (96), p. 41)

import Mathlib
import Definitions.Def_GenExactSched_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Generalized Exact Scheduling (25), corrected, realizes the rates (96)**,
Nakahira–Ferragut–Wierman, arXiv:2004.12280v2, Appendix E, p. 43 ("scheduler (25) of the form (4)
can produce identical service rates to (96)").

For `0 ≤ δ`, `0 < ε` and every job with `0 ≤ σ ≤ τ`, the corrected policy (25), `uStar`, has a
trajectory of the remaining demand starting at `σ`, and along every such trajectory the service
rate at elapsed time `s` is `v*(σ, τ, τ − s)` for almost every `s ≥ 0`.

**Formalization Note.** The printed third line of (25), "`√ε 1{x > 0}` otherwise", keeps serving a
job after its deadline when `δ/2 < √ε`, which (96) does not; `uStar` serves at rate `0` there. The
statement covers every `0 ≤ σ ≤ τ`, including `τ = 0`. -/
theorem ges_realizes (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → Produces (uStar δ ε) (vStar δ ε) σ τ := by sorry

end GenExactSched
