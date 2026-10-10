-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_step_1
-- name    : GraphLQGame.DenseApprox.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:47.023736+00:00
-- url     : https://prove2.me/theorems/377c7af0-4d4c-405d-b884-2153c5d6faa9
-- title:
--   §7.2 Step (1), p. 41 — lower bound for $J_v(\beta,\boldsymbol\alpha^{-v})$ by the own-state cost, a variance term and a Cauchy–Schwarz term
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, $v$ a vertex with $\deg_G(v)\ge1$ and $\beta\in\mathcal A_G$ an admissible deviation. Let $\boldsymbol Y$ solve the state equation for $(\beta,\boldsymbol\alpha^{-v})$, where $\boldsymbol\alpha$ is the mean-field profile, with $\boldsymbol Y(0)=0$, and assume $\mathbb E\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt<\infty$. Then
--   $$J_v(\beta,\boldsymbol\alpha^{-v})\ge\frac12\mathbb E\Big[\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt+c|Y_v(T)|^2\Big]+\frac{c\sigma^2T}{2\deg_G(v)(1+cT)}-c\sqrt{\frac{\sigma^2T^2}{\deg_G(v)(1+cT)}\,\mathbb E\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt}.$$
--
--   This is the first of the three steps that prove the bound (7.5).
--
--   **Formalization Note** The finite-energy assumption is what makes the right side meaningful (otherwise it reads $\infty-\infty$); with infinite energy the cost is infinite anyway. The subtracted square-root term is moved to the left side, so the inequality is stated in $[0,\infty]$ without subtraction. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, Step (1), p. 41 (proved in Step 1, p. 42)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **Step (1)** of the proof of Theorem 2.11 (Lacker–Soret, arXiv:2005.14102v2, §7.2, p. 41):
for a non-isolated vertex `v` and an admissible deviation `β ∈ 𝒜`, with `Y` the state process of
the deviated profile `(β, α^{−v})` (zero initial states, `Y_i = X_i` for `i ≠ v`),
`J_v(β, α^{−v}) ≥ ½ E[∫₀ᵀ |β(t, Y(t))|² dt + c |Y_v(T)|²] + cσ²T / (2 deg_G(v)(1 + cT))
  − c √( σ²T² / (deg_G(v)(1 + cT)) · E ∫₀ᵀ |β(t, Y(t))|² dt )`.

Formalization Note: `S'` is any solution of the deviated system, `ownCost c T S' v` is
`½ E[∫₀ᵀ |β(t, Y(t))|² dt + c |Y_v(T)|²]` and `energy T S' v` is `E ∫₀ᵀ |β(t, Y(t))|² dt`. The
display is meaningful only when this energy is finite, which is assumed (`≠ ⊤`) and then read as a
real number; the subtracted square-root term, finite, is moved to the left side so that the
inequality lives in `ℝ≥0∞` without subtraction. Vertices are `Fin n`; initial states are `0`. -/
theorem step_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (v : Fin n) (hv : 1 ≤ G.degree v)
    (β : ℝ → SDEState n → ℝ) (hβ : GraphLQGame.Equilibrium.IsAdmissible T β)
    (S' : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v β))
    (hE : energy T S' v ≠ ⊤) :
    ownCost c T S' v + ENNReal.ofReal (c * σ ^ 2 * T / (2 * (G.degree v : ℝ) * (1 + c * T))) ≤
      GraphLQGame.Equilibrium.cost G c T S' v +
        ENNReal.ofReal (c * Real.sqrt (σ ^ 2 * T ^ 2 / ((G.degree v : ℝ) * (1 + c * T)) *
          (energy T S' v).toReal)) := by sorry

end GraphLQGame.DenseApprox
