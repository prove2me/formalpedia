-- Prove2me | Theorems.Thm_LeiBR_Sync_eq_9
-- name    : LeiBR.Sync.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:32.461639+00:00
-- url     : https://prove2.me/theorems/2b34d211-bd06-4b3f-93f4-5a2d941b0934
-- title:
--   (9) — under $\|\Gamma\|<1$ the proximal BR map contracts the Euclidean norm of block distances by $a=\|\Gamma\|$
-- statement:
--   Under Assumptions 1 and 2, with $\mu>0$, let $a=\|\Gamma\|$ be the spectral norm of the matrix (3). Then for all $y,y'\in X$,
--   $$\left\|\begin{pmatrix}\|\hat x_1(y')-\hat x_1(y)\|\\ \vdots\\ \|\hat x_N(y')-\hat x_N(y)\|\end{pmatrix}\right\|\le a\left\|\begin{pmatrix}\|y_1'-y_1\|\\ \vdots\\ \|y_N'-y_N\|\end{pmatrix}\right\|,$$
--   where the outer norms are Euclidean norms on $\mathbb R^N$.
--
--   Since $a<1$ by Assumption 2, the proximal BR map is a contraction of $X$ in this metric; this is the form of (5) used in the rate analysis.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, §3.2, (9), p. 7

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame

open MeasureTheory

namespace LeiBR.Sync

/-- (9), §3.2, p. 7: under Assumption 2, with `a = ‖Γ‖` (spectral norm), the proximal BR map
contracts the Euclidean norm of the vector of block distances:
`‖(‖x̂_i(y') - x̂_i(y)‖)_i‖ ≤ a ‖(‖y'_i - y_i‖)_i‖` for all `y, y' ∈ X`. -/
theorem eq_9
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ) :
    ∀ y ∈ stratSet X, ∀ y' ∈ stratSet X,
      blockDist (xhat y') (xhat y) ≤ specNorm (Gamma X (payoff P ξ ψ) μ) * blockDist y' y := by sorry

end LeiBR.Sync
