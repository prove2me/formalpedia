-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_lemma_2
-- name    : HiringLP.ProbeTopK.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:17.770837+00:00
-- url     : https://prove2.me/theorems/d97c4595-a2f1-4db3-b026-dd857cfb90bc
-- title:
--   Lemma 2 — a basic feasible solution of LPptk has at most two fractional y_i, and two fractional ones sum to 1
-- statement:
--   Let $I$ be a valid ProbeTop-k instance ($1 \le k \le T \le n$, non-negative values $r_j$, probability vectors $q_i$) and let $(x, y)$ be a basic feasible solution of $\mathrm{LP}_{ptk}(I)$, that is, an extreme point of its feasible polytope. Let
--
--   $$
--   F = \{\, i \in [n] : 0 < y_i < 1 \,\}
--   $$
--
--   be the set of non-integer components of $y$. Then
--
--   1. $|F| \le 2$, and
--   2. if $|F| = 2$, then $\sum_{i \in F} y_i = 1$.
--
--   This is what makes the two-point rounding DR possible: a basic solution needs to randomise over at most two applicants, and when it does, exactly one of them is interviewed.
--
--   **Formalization Note.** Since $0 \le y_i \le 1$ on the feasible set, "non-integer" is $0 < y_i < 1$. Basic feasible solutions are Mathlib's `Set.extremePoints ℝ` of the feasible set in $(x,y)$-space, which coincide with basic feasible solutions for a polytope given by linear inequalities.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 16, Lemma 2

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model

namespace HiringLP.ProbeTopK

theorem lemma_2 {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) :
    (fracSet y).card ≤ 2 ∧ ((fracSet y).card = 2 → ∑ i ∈ fracSet y, y i = 1) := by sorry

end HiringLP.ProbeTopK
