-- Prove2me | Theorems.Thm_MatroidEquitability_Supplement_theorem_19
-- name    : MatroidEquitability.Supplement.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:27:44.424785+00:00
-- url     : https://prove2.me/theorems/c400b75f-275f-40bf-ad3b-8c0cbb92467d
-- title:
--   Theorem 19 — a counterexample to the weighted carpool conjecture
-- statement:
--   For every integer $k\ge4$ there are a fractional assignment $x\in[0,1]^{(3k+1)\times 6k}$ (every column sums to $1$) and weights $d\in\mathbb R^{6k}_{\ge0}$ with $\max_jd_j=10k+3$ such that every assignment $y\in\{0,1\}^{(3k+1)\times6k}$ (every column sums to $1$, and $y_{ij}=0$ whenever $x_{ij}=0$) satisfies
--   $$\max_{i,t}\Bigl|\sum_{j=1}^t d_jy_{ij}-\sum_{j=1}^t d_jx_{ij}\Bigr|\ \ge\ 11k=\frac{11k}{10k+3}\cdot\max_jd_j ,$$
--   where $i$ ranges over the $3k+1$ rows and $t$ over $[6k]$.
--
--   Since $11k/(10k+3)>1$ for $k\ge4$, the weighted carpool conjecture (Conjecture 3) fails with constant $1$; the ratio tends to $11/10$.
--
--   **Formalization Note** The maximum over the finitely many pairs $(i,t)$ is stated as the existence of a pair, and $\max_jd_j=10k+3$ as "$10k+3$ is the greatest weight". Columns are ordered as in `Fin (6k)`.
--
--   Differences from the source:
--   - encoding: $x\in[0,1]^{(3k+1)\times6k}$, $y\in\{0,1\}^{(3k+1)\times6k}$, $t\in[6k]$, $\max_{i,t}$, $\max_j$ → real matrices on `Fin (3k+1) × Fin (6k)`, $1\le t\le6k$ with prefix $\{j:\ j.\mathrm{val}<t\}$, an existential over $(i,t)$, `IsGreatest`; reason: Lean convention, same statement.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Theorem 19 and the convention before it, p.21 (PDF p.23); proof pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_MatroidEquitability_Supplement_Assignment

namespace MatroidEquitability

namespace Supplement

/-- **Theorem 19** (printed p.21 = PDF p.23 of Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and
Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)): counterexample to
the weighted carpool Conjecture 3. For every integer `k ≥ 4` there are a fractional assignment
`x ∈ [0, 1]^{(3k+1)×6k}` and weights `d ∈ ℝ^{6k}_{≥0}` with `max_j d_j = 10k + 3` such that every assignment
`y ∈ {0, 1}^{(3k+1)×6k}` has `max_{i,t} |Σ_{j=1}^t d_j y_ij − Σ_{j=1}^t d_j x_ij| ≥ 11k = (11k/(10k + 3))·max_j d_j`.

**Formalization Note.** Following the convention stated before the theorem (p.21), an assignment must
vanish wherever `x` does (`IsAssignment x y`). `t` ranges over `[6k] = {1, …, 6k}` and the prefix
`{1, …, t}` of columns is `{j : j.val < t}` in `Fin (6k)`. The maximum over the finitely many `(i, t)` is
expressed as the existence of a pair. -/
theorem theorem_19 (k : ℕ) (hk : 4 ≤ k) :
    ∃ (x : Fin (3 * k + 1) → Fin (6 * k) → ℝ) (d : Fin (6 * k) → ℝ),
      IsFractionalAssignment x ∧ (∀ j, 0 ≤ d j) ∧ IsGreatest (Set.range d) (10 * k + 3) ∧
      (∀ y : Fin (3 * k + 1) → Fin (6 * k) → ℝ, IsAssignment x y →
        ∃ (i : Fin (3 * k + 1)) (t : ℕ), 1 ≤ t ∧ t ≤ 6 * k ∧
          (11 * k : ℝ) ≤ |prefixDisc d x y i t|) ∧
      (11 * k : ℝ) = 11 * k / (10 * k + 3) * (10 * k + 3) := by sorry

end Supplement

end MatroidEquitability
