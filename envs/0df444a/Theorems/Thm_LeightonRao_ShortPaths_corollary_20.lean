-- Prove2me | Theorems.Thm_LeightonRao_ShortPaths_corollary_20
-- name    : LeightonRao.ShortPaths.corollary_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:10.267767+00:00
-- url     : https://prove2.me/theorems/60744ced-1ccc-4c4b-8596-0b0d4f2fbbb4
-- title:
--   Corollary 20, p. 808 — a large component with two small radii
-- statement:
--   Let $G$ be a connected capacitated graph with $n\ge2$ vertices, total capacity $C$, and uniform sparsest cut value $\mathcal S$. Let $d$ be a nonnegative symmetric distance function whose total weight $W$ satisfies $0<W\le\mathcal S/(36\log_2 n)$. Then some component $T$ contains at least two thirds of the vertices, and one center reaches each vertex of $T$ by a path within $T$ with
--
--   $$|T|\ge\frac{2n}{3},\qquad
--     \text{edge radius}\le\frac{C}{2Wn^2},\qquad
--     \text{distance radius}\le\frac{1}{2n^2}.$$
--
--   This is the large low-radius region needed to connect short paths between arbitrary pairs.
--
--   **Formalization Note** The printed fraction $W\le\mathcal S/36\log n$ is read as $W\le\mathcal S/(36\log n)$, as used in its proof. The additional $W>0$ is necessary because the printed edge radius divides by $W$.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 808, Corollary 20 and footnote 8

import Mathlib
import Definitions.Def_LeightonRao_ShortPaths_Setting

namespace LeightonRao.ShortPaths

/-- Corollary 20, p. 808. -/
theorem corollary_20 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (hW : 0 < totalWeight N d)
    (hWS : totalWeight N d ≤ minCut N /
      (36 * Real.logb 2 (Fintype.card V : ℝ))) :
    ∃ T : Finset V,
      2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ) ∧
      HasRadii N d T
        (totalCap N / (2 * totalWeight N d * (Fintype.card V : ℝ) ^ 2))
        (1 / (2 * (Fintype.card V : ℝ) ^ 2)) := by sorry

end LeightonRao.ShortPaths
