-- Prove2me | Theorems.Thm_HiringLP_Parallel_list_properties
-- name    : HiringLP.Parallel.list_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:48.067177+00:00
-- url     : https://prove2.me/theorems/e2895d46-a4f9-4fd7-b94a-e928ba3d0749
-- title:
--   §5.2, p. 23 — GKPS rounding of a feasible LP_par solution: every list has ≤ T candidates, every candidate is on ≤ 1 list
-- statement:
--   Let $I=(k,T,n,p,v)$ be a Parallel Offering instance, let $y$ be a feasible solution of $\mathrm{LP}_{\mathrm{par}}(I)$, and let $Y$ be drawn from a GKPS rounding of $y$ on the complete bipartite graph candidates $\times$ positions (properties (P1)–(P3)). Then, with probability $1$,
--
--   1. **(a)** every list has at most $T$ candidates: $\sum_{i=1}^n Y_{ij}\le T$ for every position $j$;
--   2. **(b)** every candidate is on at most one list: $\sum_{j=1}^k Y_{ij}\le 1$ for every candidate $i$.
--
--   These two properties make the rounded lists a valid non-adaptive policy for the Parallel Offering problem: no candidate receives two offers and no list needs more than the $T$ available rounds.
--
--   **Formalization Note** "With probability 1" is "for every edge set $Y$ with $\mu(Y)\neq0$"; the list sizes are the vertex degrees of $Y$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 23, §5.2, properties (a) and (b)

import Mathlib
import Definitions.Def_HiringLP_Parallel_Model

namespace HiringLP.Parallel

/-- §5.2, p. 23, properties (a) and (b): if `y` is feasible for `LP_par(I)` and `μ` has the
properties (P1)–(P3) of the GKPS rounding with weights `y`, then with probability 1 the rounded
lists satisfy (a) every list `{i : Y_ij = 1}` has at most `T` candidates and (b) every candidate is
on at most one list. -/
theorem list_properties {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ)
    (hy : LPFeasible I y) (μ : Finset (Fin n × Fin k) → ℝ) (hμ : IsGKPS y μ)
    (Y : Finset (Fin n × Fin k)) (hY : μ Y ≠ 0) :
    (∀ j, degRight Y j ≤ I.T) ∧ ∀ i, degLeft Y i ≤ 1 := by sorry

end HiringLP.Parallel
