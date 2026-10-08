-- Prove2me | Theorems.Thm_OptStopC1_TimeDeriv_limsup_5_20
-- name    : OptStopC1.TimeDeriv.limsup_5_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:49.329904+00:00
-- url     : https://prove2.me/theorems/ea37203c-71a8-4b08-8bc7-3cd9407a2bac
-- title:
--   (5.20), p. 21 — lim sup V_t(t_n, x_n) ≤ G_t(z) along C ∋ (t_n, x_n) → z
-- statement:
--   Consider the finite-horizon optimal stopping problem (2.2) for the time-space process $X^{t,x}_s=(t+s,X^x_s)$. Assume that it is well posed and that the hypotheses (5.9)–(5.11) of Theorem 15 hold, with a continuous stochastic flow in the space variable. Let $z\in\partial C$ be a boundary point at which the local conditions (5.12)–(5.13) hold and which is probabilistically regular for the interior $D^\circ$ of the stopping set.
--
--   Then for every sequence $(t_n,x_n)\in C$ converging to $z$,
--   $$\limsup_{n\to\infty}V_t(t_n,x_n)\ \le\ G_t(z).$$
--
--   This is the upper half of the time-derivative smooth fit at $z$. Together with (5.17) it gives $V_t(t_n,x_n)\to G_t(z)$.
--
--   **Formalization Note** The lim sup is stated without extended reals: for every $b>G_t(z)$, eventually $V_t(t_n,x_n)<b$. The statement is for every $d\ge1$ and for general $\Lambda$ (part (II) of the proof, pp. 22–23). The paper's proof is written for $d=1$ "for ease of notation".
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 21, (5.20), proof of Theorem 15, extended to Λ ≠ 0 on pp. 22–23

import Mathlib
import Definitions.Def_OptStopC1_TimeDeriv_Flow
import Definitions.Def_OptStopC1_TimeDeriv_Problem
import Definitions.Def_OptStopC1_TimeDeriv_Generator
import Definitions.Def_OptStopC1_TimeDeriv_Hypotheses

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace OptStopC1.TimeDeriv

/-- Theorem 15, step (5.20) (p. 21, extended to general `Λ` on pp. 22–23): under the hypotheses
of Theorem 15 at a boundary point `z` that is probabilistically regular for `D°`, along every
sequence `(tₙ, xₙ) ∈ C` converging to `z`, `lim sup ∂_tV(tₙ, xₙ) ≤ ∂_tG(z)`. -/
theorem limsup_5_20 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (M : StoppingProblem m Ω) (c : GenCoeffs m)
    (hM : M.Thm15Global c) (z : ℝ × Space m) (hz : z ∈ M.boundary)
    (hloc : M.Thm15AtPoint c z)
    (hPR : IsProbRegular M.P M.T M.X (interior M.stoppingSet) z)
    (q : ℕ → ℝ × Space m) (hqC : ∀ n, q n ∈ M.contSet) (hq : Tendsto q atTop (𝓝 z)) :
    ∀ b : ℝ, timeDeriv M.T M.G z < b → ∀ᶠ n in atTop, timeDeriv M.T M.value (q n) < b := by sorry

end OptStopC1.TimeDeriv
