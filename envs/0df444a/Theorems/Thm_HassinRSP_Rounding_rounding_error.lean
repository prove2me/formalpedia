-- Prove2me | Theorems.Thm_HassinRSP_Rounding_rounding_error
-- name    : HassinRSP.Rounding.rounding_error
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:24:53.285688+00:00
-- url     : https://prove2.me/theorems/08dec22b-a88a-42d0-a0e9-db5448ffb44b
-- title:
--   §3, TEST(V), p. 38 — rounding decreases each edge-length by at most Vε/(n − 1) and each path-length by at most Vε
-- statement:
--   Consider an instance of the restricted shortest path problem: vertices $1,\dots,n$ with $n\ge 2$, edges $(i,j)$ with $i<j$, and positive integer lengths $c_{ij}$. Let $\varepsilon>0$ and $V>0$, and put $\delta=V\varepsilon/(n-1)$. TEST(V) replaces each length $c_{ij}$ by $\delta\lfloor c_{ij}/\delta\rfloor=\delta\,\tilde c^V_{ij}$, where $\tilde c^V_{ij}=\lfloor c_{ij}(n-1)/(V\varepsilon)\rfloor$.
--
--   Then for every edge $(i,j)\in E$,
--   $$\delta\,\tilde c^V_{ij}\le c_{ij}\qquad\text{and}\qquad c_{ij}-\delta\,\tilde c^V_{ij}\le \delta,$$
--   and for every path $p$ in $E$ (between any two vertices), with $\tilde c^V(p)$ the sum of the rounded lengths of its edges,
--   $$\delta\,\tilde c^V(p)\le c(p)\qquad\text{and}\qquad c(p)-\delta\,\tilde c^V(p)\le V\varepsilon .$$
--
--   In the paper's words: "This decreases each edge-length by at most $V\varepsilon/(n-1)$, and each path-length by at most $V\varepsilon$." The path bound rests on the fact that, because every edge goes from a smaller to a larger vertex, a path has at most $n-1$ edges. Both TEST(V) and the final step of the Rounding Algorithm rely on this error estimate.
--
--   **Formalization Note.** The time bound $T$ and the upper bound $\varepsilon<1$ play no role and are omitted. The path bound is stated for paths between arbitrary vertices, as in the paper's "each path-length".
-- source:
--   Hassin, Approximation schemes for the restricted shortest path problem, Math. Oper. Res. 17 (1992), p. 38, §3, paragraph after the rounding formula

import Mathlib
import Definitions.Def_HassinRSP_Rounding_Setting

namespace HassinRSP.Rounding

theorem rounding_error (I : Instance) (hI : I.WellFormed) (ε : ℝ) (hε0 : 0 < ε)
    (V : ℝ) (hV : 0 < V) :
    (∀ e ∈ I.E, V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ I.c e ∧
      (I.c e : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundLen I ε V e ≤ V * ε / ((I.n : ℝ) - 1)) ∧
    (∀ (i j : ℕ) (p : List ℕ), IsPathIn I.E i j p →
      V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ pathLen I p ∧
      (pathLen I p : ℝ) - V * ε / ((I.n : ℝ) - 1) * roundPathLen I ε V p ≤ V * ε) := by sorry

end HassinRSP.Rounding
