-- Prove2me | Theorems.Thm_OfflineStochMatch_InfinitePatience_min_at_zero
-- name    : OfflineStochMatch.InfinitePatience.min_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:59.434884+00:00
-- url     : https://prove2.me/theorems/b00d87f8-810a-4a27-81b3-1984f63a9566
-- title:
--   §3.3, p. 16 — for ã_exp, ã_lin with α = 1/2, ã(y_e)∫₀¹ e^{−2x(1−y_e)}dx is minimized over y_e ∈ [0,1] at y_e = 0
-- statement:
--   Let $\tilde a$ be the exponential attenuation function $\tilde a(z)=e^{-z/2}$ or the linear one $\tilde a(z)=1-z/2$ (Definition 4 with $\alpha=1/2$). Then the function
--   $$z\longmapsto \tilde a(z)\int_0^1 e^{-2x(1-z)}\,dx$$
--   attains its minimum over $z\in[0,1]$ at $z=0$, where its value is $\int_0^1e^{-2x}\,dx=\tfrac12(1-e^{-2})\approx 0.432$.
--
--   When every patience is $\infty$, $\tilde a(y_e)\int_0^1e^{-2x(1-y_e)}dx$ is the paper's lower bound on $a(e)\Pr[e\text{ is safe}]$; this minimization turns it into the constant of Corollary 5.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 16, §3.3, first paragraph

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting

namespace OfflineStochMatch.InfinitePatience

/-- §3.3, p. 16: for the exponential and the linear attenuation functions with `α = 1/2`, the lower
bound `ã(y_e) ∫_0^1 e^{-2x(1-y_e)} dx` on `a(e) Pr[e is safe]` is minimized over `y_e ∈ [0,1]` at
`y_e = 0`. -/
theorem min_at_zero (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    IsMinOn (fun z => aT z * ∫ x in (0 : ℝ)..1, Real.exp (-2 * x * (1 - z))) (Set.Icc (0 : ℝ) 1) 0 := by sorry

end OfflineStochMatch.InfinitePatience
