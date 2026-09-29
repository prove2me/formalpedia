-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
-- name    : LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/25d80710-6b8d-5dab-870f-1152f6ac945e
-- title:
--   Siegel set covering of GL₃(ℝ) modulo GL₃(ℤ)
-- statement:
--   There exist real constants $c$ and $C$ with $c > 0$ such that for every $M \in \mathrm{GL}_3(\mathbb{R})$ one can find $\gamma \in \mathrm{GL}_3(\mathbb{Z})$ and three elements $n, t, k \in \mathrm{GL}_3(\mathbb{R})$ with the following properties. First, the image of $\gamma$ under the map of general linear groups induced by the ring homomorphism $\mathbb{Z} \to \mathbb{R}$, multiplied on the right by $M$, equals $n t k$. Second, for all indices $i, j \in \{0,1,2\}$ the underlying matrix of $n$ satisfies $n_{ii} = 1$, satisfies $n_{ij} = 0$ whenever $j < i$, and satisfies $\lVert n_{ij} \rVert \le C$; thus $n$ is upper unitriangular with all entries bounded in absolute value by $C$ (no positivity is required of $C$, which is forced to be at least $1$ by the diagonal conditions). Third, $t_{ij} = 0$ for $i \ne j$ and $t_{ii} > 0$ for each $i$, so $t$ is diagonal with positive entries, and the two consecutive ratios satisfy $c \le t_{00}/t_{11}$ and $c \le t_{11}/t_{22}$. Fourth, $k^{\mathsf{T}} k = 1$, i.e. $k$ is orthogonal. The constants $c$ and $C$ are uniform in $M$.
--
--   This is Minkowski–Hermite reduction for ternary lattices in its group-theoretic form: $\mathrm{GL}_3(\mathbb{R})$ is covered by the $\mathrm{GL}_3(\mathbb{Z})$-translates of a Siegel set $\{ntk\}$ with bounded unipotent part and diagonal part of bounded consecutive ratios. It is used, via [`LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_compact`](thm.html#LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_compact), as the archimedean reduction-theory input in the cubic-induction part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real.lean

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix

theorem LanglandsTunnell.CubicInduction.exists_mul_eq_unipotent_mul_diagonal_mul_orthogonal_real :
    ∃ c C : ℝ, 0 < c ∧ ∀ M : GL (Fin 3) ℝ,
      ∃ (γ : GL (Fin 3) ℤ) (n t k : GL (Fin 3) ℝ),
        Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) γ * M = n * t * k ∧
        (∀ i j : Fin 3,
          (n : Matrix (Fin 3) (Fin 3) ℝ) i i = 1 ∧ (j < i → (n : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
          ‖(n : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j → (t : Matrix (Fin 3) (Fin 3) ℝ) i j = 0) ∧
        (∀ i : Fin 3, 0 < (t : Matrix (Fin 3) (Fin 3) ℝ) i i) ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 0 0 / (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 ∧
        c ≤ (t : Matrix (Fin 3) (Fin 3) ℝ) 1 1 / (t : Matrix (Fin 3) (Fin 3) ℝ) 2 2 ∧
        (k : Matrix (Fin 3) (Fin 3) ℝ)ᵀ * (k : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by sorry
