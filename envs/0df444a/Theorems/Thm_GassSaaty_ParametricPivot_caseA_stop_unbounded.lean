-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_caseA_stop_unbounded
-- name    : GassSaaty.ParametricPivot.caseA_stop_unbounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:32.665976+00:00
-- url     : https://prove2.me/theorems/2015ed3f-8f72-4039-964e-36c657a2b10d
-- title:
--   Case A stop — if $\beta_s > 0$ attains $\bar\lambda$ and all $y_{is} \le 0$, there is no minimum for $\lambda > \bar\lambda$
-- statement:
--   In Section 2's nondegenerate Case A, let $B$ be a basis with basic feasible solution $x$ of $Ax = b$, $x \ge 0$. Assume that the inequalities $\alpha_j+\lambda\beta_j\le 0$ are consistent, and let $s$ be an index with $\beta_s > 0$ attaining the finite value $\bar\lambda = \min_{\beta_j > 0}(-\alpha_j/\beta_j) = -\alpha_s/\beta_s$. If
--
--   $$
--   y_{is} \le 0 \qquad (i = 1, \dots, m),
--   $$
--
--   then for every $\lambda > \bar\lambda$ the problem "minimize $(d + \lambda d')^{\top} x$ subject to $Ax = b$, $x \ge 0$" has no minimum: its cost is unbounded below on the feasible set, and no feasible point minimizes it.
--
--   The paper: "If $y_{is} \le 0$, $i = 1, \dots, m$, then we know from the simplex method and the definition of $\bar\lambda$ that our problem has no minimum for $\lambda > \bar\lambda$; thus we are finished."
--
--   **Formalization Note** "No minimum", obtained "from the simplex method", is read as the simplex method's unbounded outcome: the optimal value `lpValue` (valued in `EReal`, from the platform) is $-\infty$ ($\bot$), and, as stated explicitly in the second conjunct, no feasible point is optimal. Nondegeneracy and Case A consistency are retained from the section setup. The hypothesis that $s$ attains the minimum in (5) is the paper's.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 41, Section 2, Case A, first paragraph

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem caseA_stop_unbounded {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x)
    (hcons : ∃ t₀ : ℝ, ∀ j, alpha A d B j + t₀ * beta A d' B j ≤ 0)
    (s : Fin n) (hβs : 0 < beta A d' B s)
    (hsmin : ∀ j, 0 < beta A d' B j →
      -alpha A d B s / beta A d' B s ≤ -alpha A d B j / beta A d' B j)
    (hcol : ∀ i, pivotColumn A B s i ≤ 0) :
    ∀ t : ℝ, -alpha A d B s / beta A d' B s < t →
      lpValue (d + t • d') (stdPolyhedron A b) = ⊥ ∧
        ¬ ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y := by sorry

end GassSaaty.ParametricPivot
