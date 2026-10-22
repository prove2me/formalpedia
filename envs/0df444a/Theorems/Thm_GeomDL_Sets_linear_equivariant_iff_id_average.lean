-- Prove2me | Theorems.Thm_GeomDL_Sets_linear_equivariant_iff_id_average
-- name    : GeomDL.Sets.linear_equivariant_iff_id_average
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:26.416002+00:00
-- url     : https://prove2.me/theorems/df641b43-4488-4830-9da4-8d6f3ebebc6b
-- title:
--   §4.1, p. 33 — a linear map on ℝⁿ is permutation equivariant iff it is α·I + β·(1/n)𝟙𝟙ᵀ
-- statement:
--   Let $n\ge1$ and let $\mathbf F:\mathbb R^n\to\mathbb R^n$ be linear. Then $\mathbf F$ is permutation equivariant,
--
--   $$\mathbf F\mathbf P x=\mathbf P\mathbf F x\quad\text{for every }n\times n\text{ permutation matrix }\mathbf P\text{ and every }x\in\mathbb R^n,$$
--
--   if and only if there are scalars $\alpha,\beta\in\mathbb R$ with
--
--   $$\mathbf F x=\alpha\,x+\beta\,\tfrac1n\mathbf 1\mathbf 1^\top x\qquad\text{for all }x\in\mathbb R^n,$$
--
--   that is, $\mathbf F$ is a linear combination of the two generators, the identity $\mathbf F_1x=x$ and the average $\mathbf F_2x=\tfrac1n\mathbf 1\mathbf 1^\top x$, all of whose entries equal $\tfrac1n\sum_{u=1}^n x_u$.
--
--   Equivalently, the commutant of the permutation representation of $\Sigma_n$ on $\mathbb R^n$ is spanned by $\mathbf I$ and $\mathbf 1\mathbf 1^\top$. This characterises the linear layers of Deep Sets.
--
--   **Formalization Note** The statement is for one feature channel ($d=d'=1$); the multi-channel form is a separate item of this mission, because the book's scalar form is false for $d>1$. The hypothesis $n\ge1$ makes $1/n$ meaningful. For $n=1$ the two generators coincide and only existence of $\alpha,\beta$ is claimed.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, p. 33, "any such map can be written as a linear combination of two generators"

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §4.1, p. 33: a linear map `F : ℝⁿ → ℝⁿ` (one channel) is permutation equivariant,
`F(Px) = P F(x)` for every permutation matrix `P`, if and only if it is a linear combination
of the identity `F₁x = x` and the average `F₂x = (1/n)𝟙𝟙ᵀx`. -/
theorem linear_equivariant_iff_id_average {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), F (permVec σ x) = permVec σ (F x)) ↔
      ∃ α β : ℝ, ∀ x : Fin n → ℝ, F x = α • x + β • average x := by sorry

end GeomDL.Sets
