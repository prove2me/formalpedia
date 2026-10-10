-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_step_3
-- name    : GraphLQGame.DenseApprox.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:52.730195+00:00
-- url     : https://prove2.me/theorems/fc07e1cc-64d6-4eb2-ab2a-b96adb55169d
-- title:
--   §7.2 Step (3), p. 41 — the own-state cost of a deviation is at least $J_v(\boldsymbol\alpha^{\mathrm{MF}})-c\sigma^2T/(2\deg_G(v)(1+cT))$
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, $v$ a vertex with $\deg_G(v)\ge1$, $\boldsymbol\alpha^{\mathrm{MF}}$ the mean-field profile and $\beta\in\mathcal A_G$ an admissible deviation. Let $\boldsymbol Y$ solve the state equation for $(\beta,\boldsymbol\alpha^{-v})$ with $\boldsymbol Y(0)=0$. Then
--   $$\frac12\mathbb E\Big[\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt+c|Y_v(T)|^2\Big]\ge J_v(\boldsymbol\alpha^{\mathrm{MF}})-\frac{c\sigma^2T}{2\deg_G(v)(1+cT)}.$$
--
--   This is the third step of the proof of (7.5); with Steps (1) and (2) it gives the deviation bound $\epsilon^G_v$.
--
--   **Formalization Note** $J_v(\boldsymbol\alpha^{\mathrm{MF}})$ is computed on any solution of the state equation for the mean-field profile, and the left side on any solution for the deviated profile. The subtracted term is moved to the other side, so the inequality is stated in $[0,\infty]$. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, Step (3), p. 41 (proved in Step 3, pp. 42–43)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **Step (3)** of the proof of Theorem 2.11 (Lacker–Soret, arXiv:2005.14102v2, §7.2, p. 41):
for a non-isolated vertex `v`, an admissible deviation `β ∈ 𝒜` and `Y` the state process of
`(β, α^{−v})`,
`½ E[∫₀ᵀ |β(t, Y(t))|² dt + c |Y_v(T)|²] ≥ J_v(α^MF) − cσ²T / (2 deg_G(v)(1 + cT))`.

Formalization Note: `S` is any solution for the mean-field profile `α^MF` (giving `J_v(α^MF)`),
`S'` any solution for the deviated profile, and `ownCost c T S' v` is the left side. The subtracted
term is moved to the left so the inequality lives in `ℝ≥0∞`. Vertices are `Fin n`; initial states
are `0`. -/
theorem step_3 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (v : Fin n) (hv : 1 ≤ G.degree v)
    (β : ℝ → SDEState n → ℝ) (hβ : GraphLQGame.Equilibrium.IsAdmissible T β)
    (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (mfProfile c T))
    (S' : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v β)) :
    GraphLQGame.Equilibrium.cost G c T S v ≤
      ownCost c T S' v + ENNReal.ofReal (c * σ ^ 2 * T / (2 * (G.degree v : ℝ) * (1 + c * T))) := by sorry

end GraphLQGame.DenseApprox
