-- Prove2me | Theorems.Thm_GraphLQGame_DenseApprox_isolated_vertex
-- name    : GraphLQGame.DenseApprox.isolated_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:25:38.828498+00:00
-- url     : https://prove2.me/theorems/9fcc4dda-d6d2-408b-8210-4208a1ae733d
-- title:
--   §7.2, p. 40 — an isolated player cannot gain by deviating from $\alpha^{\mathrm{MF}}$, so $\epsilon_v=0$
-- statement:
--   Let $G$ be a finite graph, $T,\sigma,c>0$, and let $\boldsymbol\alpha=(\alpha^{\mathrm{MF}}_i)_{i\in V}$ be the mean-field profile with zero initial states. If $v$ is an isolated vertex, $\deg_G(v)=0$, then
--   $$J_v(\boldsymbol\alpha)=\inf_{\beta\in\mathcal A_G}J_v(\beta,\boldsymbol\alpha^{-v}).$$
--   Equivalently, for every admissible $\beta$, $J_v(\boldsymbol\alpha)\le J_v(\beta,\boldsymbol\alpha^{-v})$ (the reverse inequality is the choice $\beta=\alpha^{\mathrm{MF}}_v$).
--
--   This gives $\epsilon^G_v=0$ at isolated vertices in Theorem 2.11.
--
--   **Formalization Note** The infimum is stated through all deviations, as in the definition of an $\varepsilon$-Nash equilibrium: the inequality holds for every solution of the state equation for $\boldsymbol\alpha$ and every solution for $(\beta,\boldsymbol\alpha^{-v})$. Initial states are $0$, as throughout §7.2 ((7.6) and Lemma 7.2). Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §7.2, p. 40, display before "so we may take ε_v = 0"

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_DenseApprox_MeanField

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- **Isolated vertices** (Lacker–Soret, arXiv:2005.14102v2, §7.2, p. 40, display before
"so we may take ε_v = 0"): if `deg_G(v) = 0`, then under the mean-field profile
`α = (α^MF_i)_i` (zero initial states), `J_v(α) = inf_{β ∈ 𝒜} J_v(β, α^{−v})`.

The infimum is stated through all deviations: for every admissible `β`, every solution `S` of the
state equation for `α` and every solution `S'` for `(β, α^{−v})`, `J_v(α) ≤ J_v(β, α^{−v})`
(the reverse inequality `inf ≤ J_v(α)` is the choice `β = α^MF_v`).

Formalization Note: vertices are `Fin n`; costs are `ℝ≥0∞`-valued (`cost`), and for an isolated
`v` the terminal GraphLQGame.Equilibrium.cost is `c X_v(T)²` as in (2.3). Initial states are `0`, as in §7.2 ((7.6),
Lemma 7.2); see the goal theorem's note. Solutions on different probability spaces are compared,
which is faithful by strong uniqueness for (2.1). -/
theorem isolated_vertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (v : Fin n) (hv : G.degree v = 0)
    (β : ℝ → SDEState n → ℝ) (hβ : GraphLQGame.Equilibrium.IsAdmissible T β)
    (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (mfProfile c T))
    (S' : GraphLQGame.Equilibrium.StateSol n T σ 0 (Function.update (mfProfile c T) v β)) :
    GraphLQGame.Equilibrium.cost G c T S v ≤ GraphLQGame.Equilibrium.cost G c T S' v := by sorry

end GraphLQGame.DenseApprox
