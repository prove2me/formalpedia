-- Prove2me | Theorems.Thm_GraphLQGame_Asymptotics_eq_2_7
-- name    : GraphLQGame.Asymptotics.eq_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:26:01.067837+00:00
-- url     : https://prove2.me/theorems/b785038a-4970-4908-8db5-eb97a94fcfe4
-- title:
--   (2.7) — each equilibrium state $X^G_i(t)$ is centered Gaussian with variance $\sigma^2\int_0^t\int((1-f_G(T-t)\lambda)/(1-f_G(T-s)\lambda))^2\mu_G(d\lambda)ds$
-- statement:
--   Let $G$ be a finite transitive graph on $n$ vertices without isolated vertices, let $T,\sigma,c>0$, let $f_G$ solve $f_G' = c\,Q_G'(f_G)$, $f_G(0)=0$ on $[0,T]$, and let $\boldsymbol X^G$ be the equilibrium state process of Theorem 2.5 (the solution of (2.1) under the feedback $\alpha^G$), started from $\boldsymbol X^G(0) = 0$. Then for every $t\in[0,T]$ and every vertex $i$, $X^G_i(t)$ is a centered Gaussian random variable with variance
--   $$\operatorname{Var}(X^G_i(t)) = \sigma^2\int_0^t\int_{[-2,0]}\Big(\frac{1 - f_G(T-t)\lambda}{1 - f_G(T-s)\lambda}\Big)^2\mu_G(d\lambda)\,ds = \frac{\sigma^2}{n}\sum_{k=1}^n\int_0^t\Big(\frac{1 - f_G(T-t)\lambda^G_k}{1 - f_G(T-s)\lambda^G_k}\Big)^2 ds,$$
--   where $\lambda^G_1,\dots,\lambda^G_n$ are the eigenvalues of $L_G$ and $\mu_G$ their empirical distribution. In particular all players have the same variance, equal to the average $\frac1n\sum_k\operatorname{Var}(X^G_k(t))$.
--
--   This is the finite-graph formula whose limit is the variance $V_\mu(t)$ of Theorem 2.6(2).
--
--   **Formalization Note** The law of $X^G_i(t)$ is stated as the Gaussian measure $\mathcal N(0,V)$ with $V\ge0$ (Lean's `gaussianReal` takes its variance in $\mathbb R_{\ge0}$), together with the variance identity. The middle trace expression of (2.7) is not restated. Vertices are `Fin n`.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.3, (2.7) and the sentence before it, p. 7

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

/-- **(2.7)**, Lacker–Soret, arXiv:2005.14102v2, §2.3, p. 7.

Let `G` be a finite transitive graph on `n` vertices without isolated vertices, `f_G` the solution of
the ODE of Theorem 2.5, and `X^G` the equilibrium state process started from `X^G(0) = 0`. Then for
every `t ∈ [0, T]` each `X^G_i(t)` is a centered Gaussian with the same variance
`Var(X^G_i(t)) = σ² ∫₀ᵗ ∫_{[−2,0]} ((1 − f_G(T − t)λ) / (1 − f_G(T − s)λ))² μ_G(dλ) ds`,
i.e. `(σ²/n) Σ_k ∫₀ᵗ ((1 − f_G(T − t)λ_k) / (1 − f_G(T − s)λ_k))² ds`.

Formalization Note: the eigenvalue sum of (2.7) is written as an integral against `μ_G`
(`specMeasure`), as the paper does right after (2.7) and in Theorem 2.6. Since every `X_i(t)` has
the same variance, the first equality of (2.7) (the average over `k`) follows; the middle trace
expression is not restated. Vertices are `Fin n`. -/
theorem eq_2_7 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {T σ c : ℝ}
    (hT : 0 < T) (hσ : 0 < σ) (hc : 0 < c) (htrans : GraphLQGame.Equilibrium.IsTransitive G) (hiso : GraphLQGame.Equilibrium.NoIsolated G)
    (f : ℝ → ℝ) (hf : GraphLQGame.Equilibrium.IsFSol c T (GraphLQGame.Equilibrium.QG G) f) (S : GraphLQGame.Equilibrium.StateSol n T σ 0 (GraphLQGame.Equilibrium.alphaG G c T f))
    (i : Fin n) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    S.P.map (fun ω => S.X t ω i) = gaussianReal 0 (Vmu σ c T (GraphLQGame.Equilibrium.specMeasure G) f t).toNNReal ∧
      variance (fun ω => S.X t ω i) S.P = Vmu σ c T (GraphLQGame.Equilibrium.specMeasure G) f t := by sorry

end GraphLQGame.Asymptotics
