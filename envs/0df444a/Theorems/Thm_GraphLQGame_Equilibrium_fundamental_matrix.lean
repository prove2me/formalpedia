-- Prove2me | Theorems.Thm_GraphLQGame_Equilibrium_fundamental_matrix
-- name    : GraphLQGame.Equilibrium.fundamental_matrix
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:27:55.993176+00:00
-- url     : https://prove2.me/theorems/2462a9d9-3fb7-45b8-aece-f52b51dde5ec
-- title:
--   §4.5, p. 28 — $\exp(-\int_s^tP(u)\,du) = (I - f(T-t)L)(I - f(T-s)L)^{-1}$
-- statement:
--   Let $G$ be a finite transitive graph without isolated vertices, $c,T>0$, $f$ the solution of $f'=cQ_G'(f)$, $f(0)=0$ on $[0,T]$, and $P=P_G$. For $0\le s\le t\le T$,
--   $$\exp\Big(-\int_s^tP(u)\,du\Big)=\big(I-f(T-t)L\big)\big(I-f(T-s)L\big)^{-1}.$$
--
--   This gives the fundamental solution of the linear equilibrium dynamics $dX=-P(t)X\,dt+\sigma\,dW$ and hence the mean and covariance in Theorem 2.5.
--
--   **Formalization Note** The integral is entrywise and $\exp$ is the matrix exponential.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §4.5, p. 28, display

import Mathlib
import Definitions.Def_GraphLQGame_Equilibrium_Graph
import Definitions.Def_GraphLQGame_Equilibrium_Equilibrium

namespace GraphLQGame.Equilibrium

/-- Lacker–Soret, arXiv:2005.14102v2, §4.5, p. 28, display: for `0 ≤ s ≤ t ≤ T`,
`exp(−∫_s^t P(u) du) = (I − f(T − t)L)(I − f(T − s)L)⁻¹`, where `P = P_G` from (2.5).

Formalization Note: `∫_s^t P(u) du` is the entrywise interval integral and `exp` is the matrix
exponential `NormedSpace.exp`. `f'(T − u)` inside `P_G` is written `c Q_G'(f(T − u))`. -/
theorem fundamental_matrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hT : IsTransitive G) (hN : NoIsolated G) (c T : ℝ) (hc : 0 < c) (hTpos : 0 < T)
    (f : ℝ → ℝ) (hf : IsFSol c T (QG G) f) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    NormedSpace.exp (-(Matrix.of fun j k => ∫ u in s..t, PG G c T f u j k)) =
      (1 - f (T - t) • lap G) * (1 - f (T - s) • lap G)⁻¹ := by sorry

end GraphLQGame.Equilibrium
