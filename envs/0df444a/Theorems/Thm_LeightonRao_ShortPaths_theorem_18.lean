-- Prove2me | Theorems.Thm_LeightonRao_ShortPaths_theorem_18
-- name    : LeightonRao.ShortPaths.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:39.216978+00:00
-- url     : https://prove2.me/theorems/45884dac-7549-4f73-87fa-a2a83730a3e5
-- title:
--   Theorem 18, p. 808 — a large uniform flow on short paths
-- statement:
--   There are absolute positive constants $c_1,c_2$ such that every connected undirected capacitated network on $n\ge2$ vertices, with uniform sparsest cut value $\mathcal S$ and maximum incident capacity $C_{\max}$, admits a uniform concurrent flow of value $\lambda$ routed entirely on paths of at most $L$ edges, where
--
--   $$\lambda\ge c_1\frac{\mathcal S}{\log_2 n},\qquad
--     L\le c_2\frac{C_{\max}\log_2 n}{n\mathcal S}.$$
--
--   Both constants are uniform across all finite networks. This strengthens the approximate max-flow/min-cut result by controlling the number of edges used by every flow path.
--
--   **Formalization Note** “Length” here counts edges, rather than distance-function weight. An actual flow, its value, and an integer hop limit are existential witnesses. The paper's polynomial-time claim is outside this existence statement. Each unordered unit demand is encoded as two ordered demands of $1/2$ (footnote 2, p. 791).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 808, Theorem 18

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Theorem 18, p. 808. Both asymptotic constants are absolute across all finite networks. -/
theorem theorem_18 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V),
        2 ≤ Fintype.card V → IsConnectedNet N →
        ∃ (L : ℕ) (f : V → V → ℕ → V → V → ℝ) (lam : ℝ),
          (L : ℝ) ≤ c₂ * cmax N * Real.logb 2 (Fintype.card V : ℝ) /
            ((Fintype.card V : ℝ) * minCut N) ∧
          IsShortConcurrentFlow N uniformDemand L f lam ∧
          c₁ * minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤ lam := by sorry

end LeightonRao.ShortPaths
