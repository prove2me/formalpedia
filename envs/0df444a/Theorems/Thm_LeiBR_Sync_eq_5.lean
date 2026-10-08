-- Prove2me | Theorems.Thm_LeiBR_Sync_eq_5
-- name    : LeiBR.Sync.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:17.514993+00:00
-- url     : https://prove2.me/theorems/18bc1699-baca-44fa-8173-aa00670e55b0
-- title:
--   (5) — the proximal BR map is a $\Gamma$-contraction blockwise
-- statement:
--   Let the stochastic Nash game satisfy Assumption 1, let $\mu>0$, and let $\hat x$ be the proximal best-response map and $\Gamma=[\gamma_{ij}]$ the matrix (3)–(4). Then for all profiles $y,y'\in X$, componentwise,
--   $$\begin{pmatrix}\|\hat x_1(y')-\hat x_1(y)\|\\ \vdots\\ \|\hat x_N(y')-\hat x_N(y)\|\end{pmatrix}\le\Gamma\begin{pmatrix}\|y_1'-y_1\|\\ \vdots\\ \|y_N'-y_N\|\end{pmatrix},$$
--   that is, $\|\hat x_i(y')-\hat x_i(y)\|\le\sum_{j=1}^N\gamma_{ij}\|y_j'-y_j\|$ for every player $i$.
--
--   This is the basic Lipschitz estimate of the proximal best response in terms of curvature and coupling of the payoffs; every convergence result of the paper rests on it.
--
--   **Formalization Note** The paper obtains (5) by adapting Facchinei–Pang, Section 12.6.1, and does not prove it. Assumption 1(b) is taken jointly in the profile, which (4) needs for the mixed blocks.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, §2.2, (5), p. 5

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame

open MeasureTheory

namespace LeiBR.Sync

/-- (5), §2.2, p. 5: the proximal best-response map is a `Γ`-contraction, componentwise:
`‖x̂_i(y') - x̂_i(y)‖ ≤ ∑_j γ_ij ‖y'_j - y_j‖` for all `y, y' ∈ X` and every player `i`. -/
theorem eq_5
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat) :
    ∀ y ∈ stratSet X, ∀ y' ∈ stratSet X, ∀ i : Fin N,
      ‖xhat y' i - xhat y i‖ ≤ ∑ j : Fin N, Gamma X (payoff P ξ ψ) μ i j * ‖y' j - y j‖ := by sorry

end LeiBR.Sync
