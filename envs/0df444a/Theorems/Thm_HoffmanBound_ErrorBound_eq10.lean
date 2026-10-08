-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_eq10
-- name    : HoffmanBound.ErrorBound.eq10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:17.032516+00:00
-- url     : https://prove2.me/theorems/6f2eae88-1660-4efa-9447-d4ba49548d3a
-- title:
--   (10) — if w = minᵢ(g_ii + Σ_{g_ij<0} g_ij) > 0, then |x − x₀| ≦ (a/w)||(Ax − b)⁺||
-- statement:
--   Let the system $Ax\le b$ be consistent, let $g_{ij}=A_i\cdot A_j$ be the Gram matrix of all the rows of $A$, and suppose
--   $$
--   w=\min_i\Bigl(g_{ii}+\sum_{j:\,g_{ij}<0}g_{ij}\Bigr)>0 .
--   $$
--   Let $a=\max_{i,j}|a_{ij}|$, let $|\cdot|$ be the max norm and $\|\cdot\|$ the sum norm (sum of the absolute values of the coordinates). Then for every $x\in\mathbb R^n$ there is a solution $x_0$ of $Ax\le b$ with
--   $$
--   |x-x_0|\le\frac{a}{w}\,\bigl\|(Ax-b)^+\bigr\|.
--   $$
--
--   This is the special case of Case III ($F_n=|\cdot|$, $F_m=\|\cdot\|$) singled out in Section 5.
--
--   **Formalization Note** The page prints the summation range in $w$ as "$j=1,\dots,n$"; since $g$ is an $m\times m$ matrix indexed by rows, $j$ is read as ranging over the $m$ rows. The bound is in the language of the main theorem: some solution $x_0$ satisfies it.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 265 (PDF p. 3), §5, (10)

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (10). If `Ax ≤ b` is consistent and
`w = min_i (g_ii + ∑_{j : g_ij < 0} g_ij) > 0` for the Gram matrix `g_ij = A_i · A_j` of all rows,
then with `a = max_{i,j} |a_ij|` every `x` has a solution `x₀` with
`|x - x₀| ≤ (a / w) ‖(Ax - b)⁺‖` (max norm on the left, sum norm on the right). -/
theorem eq10 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hw : 0 < wConst A) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / wConst A * sumNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound
