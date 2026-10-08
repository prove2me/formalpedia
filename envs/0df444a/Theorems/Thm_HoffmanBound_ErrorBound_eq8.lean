-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_eq8
-- name    : HoffmanBound.ErrorBound.eq8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:29.615785+00:00
-- url     : https://prove2.me/theorems/d6499917-15da-42bf-a321-e1aca05b8b38
-- title:
--   (8) — |x − x₀| ≦ c|(Ax − b)⁺| in the max norm, with c = max_{v_S>0} a_S/v_S
-- statement:
--   Let the system $Ax\le b$ be consistent and let $|\cdot|$ be the max norm. For a nonempty set $S$ of rows let $a_S$ be the largest absolute value of the coordinates of the rows $A_i$, $i\in S$ (6), and let
--   $$
--   v_S=\min_{\lambda}\max_{i\in S}\sum_{j\in S}g_{ij}\lambda_j,\qquad g_{ij}=A_i\cdot A_j,
--   $$
--   the minimum over $\lambda_j\ge 0$ with $\sum_{j\in S}\lambda_j=1$: the value of the zero-sum two-person game with matrix $(g_{ij})_{i,j\in S}$ (7). Put
--   $$
--   c=\max_{v_S>0}\frac{a_S}{v_S}.
--   $$
--   Then for every $x\in\mathbb R^n$ there is a solution $x_0$ of $Ax\le b$ with
--   $$
--   |x-x_0|\le c\,\bigl|(Ax-b)^+\bigr|.
--   $$
--
--   This makes the constant of the main theorem explicit for Case II ($F_n=F_m=|\cdot|$) in terms of matrix games.
--
--   **Formalization Note** The maximum defining $c$ ranges over the nonempty sets $S$ of rows with $v_S>0$; if there is none (every row of $A$ is $0$), $c$ is taken to be $0$, and then every $x$ is a solution of the consistent system, so the bound holds with $x_0=x$.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), pp. 264–265 (PDF pp. 2–3), §4, (6), (7), (8)

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model
import Definitions.Def_HoffmanBound_ErrorBound_NormConstants

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 265, (8). If `Ax ≤ b` is consistent, every `x` has a solution `x₀` with
`|x - x₀| ≤ c |(Ax - b)⁺|` (max norms), where `c = max_{v_S > 0} a_S / v_S` over the nonempty sets
`S` of rows, `a_S` as in (6) and `v_S` the game value (7). -/
theorem eq8 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hcons : (solutionSet A b).Nonempty) :
    ∀ x : Fin n → ℝ, ∃ x₀ ∈ solutionSet A b,
      maxNorm (x - x₀) ≤ constC8 A * maxNorm (posPartVec (A *ᵥ x - b)) := by sorry

end HoffmanBound.ErrorBound
