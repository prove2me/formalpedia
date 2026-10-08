-- Prove2me | Theorems.Thm_GassSaaty_ParametricPivot_summary4_closed_connected
-- name    : GassSaaty.ParametricPivot.summary4_closed_connected
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:42:43.047178+00:00
-- url     : https://prove2.me/theorems/59c3ddef-5621-4698-9578-ea99fef69bf2
-- title:
--   Summary (4) — the set of $\lambda$ for which minimum solutions exist is closed and connected
-- statement:
--   For the parametric linear program
--
--   $$
--   \text{minimize } (d + \lambda d')^{\top} x \quad \text{subject to } Ax = b,\ x \ge 0,
--   $$
--
--   with $A$ an $m \times n$ real matrix and $b \in \mathbb R^m$, assume the Section 2 setup: the problem is nondegenerate and a basic feasible solution is available. Let $S$ be the set of real $\lambda$ for which some feasible $x$ attains the minimum. Then $S$ is a closed and connected subset of $\mathbb R$:
--
--   $$
--   S = \{\lambda \in \mathbb R : \exists\, x \text{ minimizing } (d + \lambda d')^{\top} x \text{ over } Ax = b,\ x \ge 0\} \text{ is closed and connected.}
--   $$
--
--   So $S$ is empty, a point, or a closed interval (possibly a half-line or all of $\mathbb R$). This is item (4) of the paper's summary.
--
--   **Formalization Note** "Minimum solutions exist" is read as the existence of a feasible point satisfying `IsLpOptimal`. "Connected" is Mathlib's `IsPreconnected`. The section's standing nondegeneracy and basic feasible solution assumptions are explicit binders.
-- source:
--   Gass and Saaty, The computational algorithm for the parametric objective function, Naval Res. Logist. Quart. 2 (1955), p. 42, Summary, item (4)

import Mathlib
import Definitions.Def_GassSaaty_ParametricPivot_Parametric

open LinearOptimization

namespace GassSaaty.ParametricPivot

theorem summary4_closed_connected {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (d d' : Fin n → ℝ)
    (hnd : ∀ y, IsBasicFeasibleSolution (stdFormSystem A b) y →
      ¬ IsStdDegenerateBasicSolution A b y)
    (B : Fin m ↪ Fin n) (x : Fin n → ℝ) (hx : IsSimplexState A b B x) :
    IsClosed {t : ℝ | ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y} ∧
      IsPreconnected {t : ℝ | ∃ y, IsLpOptimal (d + t • d') (stdPolyhedron A b) y} := by sorry

end GassSaaty.ParametricPivot
