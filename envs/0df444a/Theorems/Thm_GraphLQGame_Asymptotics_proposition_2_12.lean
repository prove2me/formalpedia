-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_proposition_2_12
-- name    : GraphLQGame.Asymptotics.proposition_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:32.647068+00:00
-- url     : https://prove2.me/theorems/ba262a84-3d1a-4811-bd56-39f8586dc37f
-- title:
--   Proposition 2.12 — correlation decay $|\mathrm{Cov}(X_u(t),X_v(t))|\le 2\sigma^2t\gamma^{d(u,v)}(1+d(u,v)(1-\gamma))/(\delta(G)(1-\gamma)^2)$, $u\ne v$
-- statement:
--   Let $G$ be a finite transitive graph without isolated vertices, of common degree $\delta(G)$, let $T,\sigma,c>0$, and let $\boldsymbol X^G$ be the equilibrium state process of Theorem 2.5 from any non-random initial state. Let $d_G(u,v)$ be the graph distance and $\gamma = cT/(1+cT)\in(0,1)$. Then for distinct vertices $u\ne v$ and every $t\in[0,T]$,
--   $$|\operatorname{Cov}(X^G_u(t),X^G_v(t))|\le 2\sigma^2t\,\frac{\gamma^{d_G(u,v)}\big(1 + d_G(u,v)(1-\gamma)\big)}{\delta(G)(1-\gamma)^2}\,\mathbf 1_{\{d_G(u,v)<\infty\}}.$$
--   In particular the covariance vanishes when $u$ and $v$ lie in different connected components.
--
--   Covariances decay geometrically in the graph distance and like $1/\delta(G)$ in the degree. This is the estimate that turns convergence of one player's law into convergence of the empirical measure in Theorem 2.6(3).
--
--   **Formalization Note** The paper states (2.17) for all vertices $u,v$; for $u = v$ the bound is false for large degree (complete graph $K_n$, $t=T$: the bound is $2\sigma^2T(1+cT)^2/(n-1)$, while $\operatorname{Var}(X_u(T))\ge\sigma^2T(n-1)/(n(1+2cT))$, so it fails once $n-1>4(1+cT)^2(1+2cT)$), so this statement is for $u\ne v$ only, which is the case the paper's proof and its use in §7.1.2 need. The indicator is a case split on reachability, since Lean's graph distance is $0$ for unreachable pairs. $\delta(G)$ is the degree of $u$.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3.2, Proposition 2.12, (2.17), p. 11; proof in §6, pp. 34–37

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Game
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium
import Definitions.Def_GraphLQGame_Asymptotics_Spectral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace GraphLQGame.Asymptotics

open EthierKurtz

/-- **Proposition 2.12** (Correlation decay on transitive graphs), Lacker–Soret,
arXiv:2005.14102v2, §2.3.2, p. 11, for **distinct** vertices.

Let `G` be a finite transitive graph without isolated vertices, of common degree `δ(G)`, and `X^G`
the equilibrium state process of Theorem 2.5 (any non-random initial state). Let
`γ = cT/(1 + cT)`. For distinct vertices `u ≠ v` and `t ∈ [0, T]`,
`|Cov(X_u(t), X_v(t))| ≤ 2σ²t γ^{d(u,v)} (1 + d(u,v)(1 − γ)) / (δ(G)(1 − γ)²)` if `v` is reachable
from `u`, and `Cov(X_u(t), X_v(t)) = 0` otherwise (the indicator `1_{d(u,v) < ∞}`).

Formalization Note: as printed, (2.17) is also claimed for `u = v`, where it is false for large
degree (complete graph `K_n`, `n ≥ 2`, `t = T`: the bound is `2σ²T(1 + cT)²/(n − 1)`, while
`Var(X_u(T)) ≥ σ²T(n − 1)/(n(1 + 2cT))` by (2.7) and `f_G(s) ≤ cs`; so it fails once
`n − 1 > 4(1 + cT)²(1 + 2cT)`); this statement is for `u ≠ v` only. The
indicator is encoded by a case split on `G.Reachable u v`, since `SimpleGraph.dist` is `0` for
unreachable pairs. `δ(G)` is `G.degree u` (the graph is regular). Times are `t ∈ [0, T]`, the
horizon of (2.1). -/
theorem proposition_2_12 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (htrans : GraphLQGame.Equilibrium.IsTransitive G) (hiso : GraphLQGame.Equilibrium.NoIsolated G)
    (x0 : SDEState n) (f : ℝ → ℝ) (hf : GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG G) f)
    (S : GraphLQGame.Equilibrium.StateSol n T σ x0 (GraphLQGame.Equilibrium.alphaG G c T f)) (u v : Fin n) (huv : u ≠ v)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (G.Reachable u v →
      |covariance (fun ω => S.X t ω u) (fun ω => S.X t ω v) S.P| ≤
        2 * σ ^ 2 * t * (c * T / (1 + c * T)) ^ G.dist u v *
          (1 + (G.dist u v : ℝ) * (1 - c * T / (1 + c * T))) /
          ((G.degree u : ℝ) * (1 - c * T / (1 + c * T)) ^ 2)) ∧
    (¬ G.Reachable u v → covariance (fun ω => S.X t ω u) (fun ω => S.X t ω v) S.P = 0) := by sorry

end GraphLQGame.Asymptotics
