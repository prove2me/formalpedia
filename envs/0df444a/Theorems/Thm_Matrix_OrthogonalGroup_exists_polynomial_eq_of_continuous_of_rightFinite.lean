-- Prove2me | Theorems.Thm_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite
-- name    : Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/7243ca87-4430-5a2a-b1fb-93d0b078d718
-- title:
--   Right-finite continuous functions on O(2) are polynomials in the entries
-- statement:
--   Let $\Phi$ be a complex-valued function on the orthogonal group $O(2) = \{k \in M_2(\mathbb{R}) : k k^{\mathsf T} = 1\}$ (as a subgroup of the group of units of $M_2(\mathbb{R})$), and assume: (i) $\Phi$ is continuous; (ii) the right translates of $\Phi$ span a finite-dimensional space, in the precise sense that there is a finite family $s$ of functions $O(2) \to \mathbb{C}$ such that for every $k \in O(2)$ the function $x \mapsto \Phi(x k)$ lies in the $\mathbb{C}$-linear span of $s$. Then there is a function $F : M_2(\mathbb{R}) \to \mathbb{C}$ belonging to the $\mathbb{C}$-linear span of the set of functions of the form $m \mapsto \prod_{\varphi \in l} \varphi(m)$, where $l$ runs over finite lists of continuous $\mathbb{R}$-linear maps $M_2(\mathbb{R}) \to \mathbb{C}$ (the empty list giving the constant function $1$), such that $\Phi(k) = F(k)$ for every $k \in O(2)$, where $k$ on the right is the underlying $2 \times 2$ real matrix. Thus $\Phi$ is the restriction to $O(2)$ of a polynomial function, with complex coefficients, in the four real matrix entries.
--
--   This is the statement, at the real place, that a continuous function on the compact group $O(2)$ generating a finite-dimensional space under right translation is a matrix coefficient and hence polynomial in the entries; on the identity component $SO(2)$ it amounts to saying that $\Phi(r_\theta)$ is a trigonometric polynomial in $\theta$. It is used to verify smoothness and polynomial-growth hypotheses in the estimate [`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`](thm.html#AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean

import Mathlib.Analysis.Matrix.Normed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite
    (Φ : ↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ) (hc : Continuous Φ)
    (hfin : ∃ s : Finset (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ),
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ),
        (fun x => Φ (x * k)) ∈ Submodule.span ℂ (s : Set (↥(Matrix.orthogonalGroup (Fin 2) ℝ) → ℂ))) :
    ∃ F ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℝ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod},
      ∀ k : ↥(Matrix.orthogonalGroup (Fin 2) ℝ), Φ k = F (k : Matrix (Fin 2) (Fin 2) ℝ) := by sorry
