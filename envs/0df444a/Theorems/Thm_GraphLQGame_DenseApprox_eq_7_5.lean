-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_eq_7_5
-- name    : GraphLQGame.DenseApprox.eq_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:42.286483+00:00
-- url     : https://prove2.me/theorems/dcbd2f1c-4b7c-4ff8-a3e6-64bd453de928
-- title:
--   (7.5) — a non-isolated player gains at most $\frac{\sigma^2cT}{1+cT}\sqrt{cT(2+cT)/\deg_G(v)}$ by deviating from $\alpha^{\mathrm{MF}}$
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, $\boldsymbol\alpha$ the mean-field profile with zero initial states, and $v$ a vertex with $\deg_G(v)\ge1$. For every admissible deviation $\beta\in\mathcal A_G$,
--   $$J_v(\beta,\boldsymbol\alpha^{-v})\ge J_v(\boldsymbol\alpha)-\frac{\sigma^2cT}{1+cT}\sqrt{\frac{cT(2+cT)}{\deg_G(v)}}.$$
--
--   This is the per-vertex content of Theorem 2.11 at non-isolated vertices: the gain from a unilateral deviation decays like $\deg_G(v)^{-1/2}$.
--
--   **Formalization Note** The paper proves (7.5) for a minimizer (or $\delta$-optimizer) $\beta$ of $J_v(\cdot,\boldsymbol\alpha^{-v})$, which gives it for every admissible $\beta$; it is stated here for every admissible $\beta$, every solution for $\boldsymbol\alpha$ and every solution for $(\beta,\boldsymbol\alpha^{-v})$. The subtracted term is moved to the other side, so the inequality is stated in $[0,\infty]$. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, (7.5), p. 41

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **(7.5)** (Lacker–Soret, arXiv:2005.14102v2, §7.2, p. 41): for a non-isolated vertex `v`,
`J_v(β, α^{−v}) ≥ J_v(α) − (σ²cT/(1 + cT)) √(cT(2 + cT)/deg_G(v))`.

Stated for every admissible deviation `β ∈ 𝒜` (the page proves it for a minimizer, or a
δ-optimizer, which gives it for every `β`), every solution `S` for the mean-field profile `α` and
every solution `S'` for `(β, α^{−v})`.

Formalization Note: costs are `ℝ≥0∞`-valued; the subtracted term is moved to the right side.
Vertices are `Fin n`; initial states are `0`. -/
theorem eq_7_5 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (v : Fin n) (hv : 1 ≤ G.degree v)
    (β : ℝ → SDEState n → ℝ) (hβ : GraphLQGame.Equilibrium.IsAdmissible T β)
    (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (mfProfile c T))
    (S' : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v β)) :
    GraphLQGame.Equilibrium.cost G c T S v ≤
      GraphLQGame.Equilibrium.cost G c T S' v + ENNReal.ofReal (σ ^ 2 * c * T / (1 + c * T) *
        Real.sqrt (c * T * (2 + c * T) / (G.degree v : ℝ))) := by sorry

end GraphLQGame.DenseApprox
