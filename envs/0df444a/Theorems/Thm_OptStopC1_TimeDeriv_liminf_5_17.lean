-- Prove2me | Theorems.Thm_OptStopC1_TimeDeriv_liminf_5_17
-- name    : OptStopC1.TimeDeriv.liminf_5_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:45.951835+00:00
-- url     : https://prove2.me/theorems/ce5c29c5-b150-4f94-a041-b0514fa7adec
-- title:
--   (5.17), p. 21 — lim inf V_t(t_n, x_n) ≥ G_t(z) along C ∋ (t_n, x_n) → z
-- statement:
--   Consider the finite-horizon optimal stopping problem (2.2) for the time-space process $X^{t,x}_s=(t+s,X^x_s)$. Assume that it is well posed and that the hypotheses (5.9)–(5.11) of Theorem 15 hold, with a continuous stochastic flow in the space variable. Let $z\in\partial C$ be a boundary point at which the local conditions (5.12)–(5.13) hold and which is probabilistically regular for the interior $D^\circ$ of the stopping set.
--
--   Then for every sequence $(t_n,x_n)\in C$ converging to $z$,
--   $$\liminf_{n\to\infty}V_t(t_n,x_n)\ \ge\ G_t(z),$$
--   where $V_t=\partial V/\partial t$ and $G_t=\partial G/\partial t$.
--
--   This is the lower half of the time-derivative smooth fit at $z$. Together with (5.20) it gives $V_t(t_n,x_n)\to G_t(z)$.
--
--   **Formalization Note** The lim inf is stated without extended reals: for every $a<G_t(z)$, eventually $a<V_t(t_n,x_n)$. $V_t$ and $G_t$ are derivatives along the time line within $[0,T]$. The paper proves this step for $d=1$ "for ease of notation" (p. 20) and states that the argument works in any dimension; the statement here is for every $d\ge1$, and for general $\Lambda$ (part (II) of the proof, p. 22).
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 21, (5.17), proof of Theorem 15, extended to Λ ≠ 0 on p. 22

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace OptStopC1.TimeDeriv

/-- Theorem 15, step (5.17) (p. 21, extended to general `Λ` on p. 22): under the hypotheses of
Theorem 15 at a boundary point `z` that is probabilistically regular for `D°`, along every
sequence `(tₙ, xₙ) ∈ C` converging to `z`, `lim inf ∂_tV(tₙ, xₙ) ≥ ∂_tG(z)`. -/
theorem liminf_5_17 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c) (z : ℝ × Space m) (hz : z ∈ M.boundary)
    (hloc : M.Thm15AtPoint c z)
    (hPR : IsProbRegular M.P M.T M.X (interior M.stoppingSet) z)
    (q : ℕ → ℝ × Space m) (hqC : ∀ n, q n ∈ M.contSet) (hq : Tendsto q atTop (𝓝 z)) :
    ∀ a : ℝ, a < timeDeriv M.T M.G z → ∀ᶠ n in atTop, a < timeDeriv M.T M.value (q n) := by sorry

end OptStopC1.TimeDeriv
