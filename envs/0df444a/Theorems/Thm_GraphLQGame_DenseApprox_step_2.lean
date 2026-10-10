-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_step_2
-- name    : GraphLQGame.DenseApprox.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:33.18607+00:00
-- url     : https://prove2.me/theorems/0d448f19-260d-44bf-9ec1-1bec05b9cffd
-- title:
--   §7.2 Step (2), p. 41 — a deviation no worse than the zero control has energy at most $c\sigma^2T(2+cT)/(1+cT)$
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, $v$ a vertex with $\deg_G(v)\ge1$, $\boldsymbol\alpha$ the mean-field profile, and $\beta\in\mathcal A_G$ an admissible deviation whose cost is at most that of the zero control,
--   $$J_v(\beta,\boldsymbol\alpha^{-v})\le J_v(0,\boldsymbol\alpha^{-v}).$$
--   Let $\boldsymbol Y$ solve the state equation for $(\beta,\boldsymbol\alpha^{-v})$ with $\boldsymbol Y(0)=0$. Then
--   $$\mathbb E\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt\le c\sigma^2T\,\frac{2+cT}{1+cT}.$$
--
--   The paper states this for $\beta$ a minimizer of $J_v(\cdot,\boldsymbol\alpha^{-v})$ (or a $\delta$-optimizer), and its proof uses only the displayed comparison with the zero control. It is the second step of the proof of (7.5).
--
--   **Formalization Note** The comparison with the zero control is the hypothesis, compared across any solution of the deviated system and any solution of the system in which $v$ uses the control $0$. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, Step (2), p. 41 (proved in Step 2, p. 42)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **Step (2)** of the proof of Theorem 2.11 (Lacker–Soret, arXiv:2005.14102v2, §7.2, pp. 41–42):
`E ∫₀ᵀ |β(t, Y(t))|² dt ≤ cσ²T (2 + cT)/(1 + cT)`.

The page proves this for `β` a minimizer of `J_v(·, α^{−v})` and uses only
`J_v(β, α^{−v}) ≤ J_v(0, α^{−v})` (p. 42, "In particular"); that inequality is the hypothesis here:
for a non-isolated vertex `v`, an admissible `β`, a solution `S'` of the deviated system and a
solution `S₀` of the system where `v` uses the zero control, if `J_v(β, α^{−v}) ≤ J_v(0, α^{−v})`,
then the energy bound holds.

Formalization Note: `energy T S' v` is `E ∫₀ᵀ |β(t, Y(t))|² dt` in `ℝ≥0∞`. Vertices are `Fin n`;
initial states are `0`. The hypothesis `hopt` is the page's own (it is what the minimizer, or a
δ-optimizer as the page allows, satisfies), made explicit. -/
theorem step_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (v : Fin n) (hv : 1 ≤ G.degree v)
    (β : ℝ → SDEState n → ℝ) (hβ : GraphLQGame.Equilibrium.IsAdmissible T β)
    (S' : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v β))
    (S₀ : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v (fun _ _ => 0)))
    (hopt : GraphLQGame.Equilibrium.cost G c T S' v ≤ GraphLQGame.Equilibrium.cost G c T S₀ v) :
    energy T S' v ≤ ENNReal.ofReal (c * σ ^ 2 * T * (2 + c * T) / (1 + c * T)) := by sorry

end GraphLQGame.DenseApprox
