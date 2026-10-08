-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_eq9
-- name    : HoffmanBound.ErrorBound.eq9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:15.265215+00:00
-- url     : https://prove2.me/theorems/87d004f9-6de1-4a87-9e77-f5f1c321b29c
-- title:
--   (9) — if all A_i·A_j > 0, then |x − x₀| ≦ (a/v)|(Ax − b)⁺| in the max norm
-- statement:
--   Let the system $Ax\le b$ be consistent and suppose $A_i\cdot A_j>0$ for all rows $i,j$ (including $i=j$). Let
--   $$
--   v=\min_{i,j}A_i\cdot A_j,\qquad a=\max_{i,j}|a_{ij}|,
--   $$
--   and let $|\cdot|$ be the max norm (largest absolute value of a coordinate). Then for every $x\in\mathbb R^n$ there is a solution $x_0$ of $Ax\le b$ with
--   $$
--   |x-x_0|\le\frac{a}{v}\,\bigl|(Ax-b)^+\bigr|.
--   $$
--
--   This is the special case of Case II ($F_n=F_m=|\cdot|$) in which the constant of the main theorem is given by the entries and Gram matrix of $A$ alone.
--
--   **Formalization Note** The statement is in "the language of the theorem": for every $x$ some solution $x_0$ satisfies the bound. $v$ and $a$ are `⨅`/`⨆` over the rows and columns (see the definition file); for $m\ge 1$ they are the attained min and max.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 265 (PDF p. 3), §4, (9)

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (9). If `Ax ≤ b` is consistent and all `A_i · A_j > 0`, then with
`v = min_{i,j} A_i · A_j` and `a = max_{i,j} |a_ij|`, every `x` has a solution `x₀` with
`|x - x₀| ≤ (a / v) |(Ax - b)⁺|` (max norms). -/
theorem eq9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) (hpos : ∀ i j, 0 < A i ⬝ᵥ A j) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ aMax A / vMin A * maxNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound
