-- Prove2me | Theorems.Thm_NonlinFPE_Main_prob_density_preserved
-- name    : NonlinFPE.Main.prob_density_preserved
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:03.300708+00:00
-- url     : https://prove2.me/theorems/3b4eea75-5a8f-4e67-b60d-4290dd83439c
-- title:
--   §3.1, proof of Theorem 3.4, p. 19 — under (H1)–(H3), if u₀ is a probability density then so is u(t, u₀) for all t ≥ 0
-- statement:
--   Assume (H1)–(H3) and let $u$ be the mild solution of (3.2) in $L^1$ for the operator $A$ of (3.8)–(3.9), with $u(0) = u_0$. If $u_0$ is a probability density ($u_0 \ge 0$ a.e., $\int u_0\,dx = 1$), then
--   $$u(t) \ge 0 \ \text{a.e.}, \qquad \int_{\mathbb R^d}u(t,x)\,dx = 1, \qquad t \ge 0 .$$
--
--   This is Hypothesis 2.1 (i) for the curve $\mu_t = u(t,x)dx$, needed to apply the general scheme of §2 in Theorem 4.1.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3.1, proof of Theorem 3.4, p. 19 ("In particular, it follows that, if u₀ is a probability density …")

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

open EthierKurtz

/-- §3.1, proof of Theorem 3.4, p. 19, under (H1)–(H3): if `u₀` is a probability density, then so
is `u(t)` for every `t ≥ 0`, for the mild solution `u` of (3.2) with `u(0) = u₀`. -/
theorem prob_density_preserved {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) (hND : HypND a b γ)
    (u₀ : SDEState d →₁[volume] ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ)
    (hu : IsMildSolution (opA a b) u₀ u) (hu₀ : IsProbDensity u₀) :
    ∀ t, IsProbDensity (u t) := by sorry

end NonlinFPE.Main
