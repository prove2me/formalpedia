-- Prove2me | Theorems.Thm_Gelbart_hasse_minkowski
-- name    : Gelbart.hasse_minkowski
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T03:34:59.58524+00:00
-- url     : https://prove2.me/theorems/c0c785e5-8688-445b-964f-ec5d8b9c14a9
-- title:
--   Hasse–Minkowski: local-global principle for integral quadratic forms
-- statement:
--   **Theorem (Hasse–Minkowski).** Let $Q(x_1,\dots,x_n) = \sum_{i,j} a_{ij} x_i x_j$ be a quadratic form with symmetric integer coefficient matrix $(a_{ij})$ and $\det(a_{ij}) \ne 0$. Then $Q$ has a nontrivial integer zero if and only if it has a nontrivial real zero and a nontrivial $p$-adic zero for every prime $p$.
--
--   This is the instance of the local-global principle quoted by Gelbart in §II.A as the motivation for passing from $\mathbb{Q}$ to its completions. Symmetry of the matrix is stated explicitly here, where the source leaves it implicit in writing $\det(a_{ij})$.
-- source:
--   S. Gelbart, An elementary introduction to the Langlands program, Bull. Amer. Math. Soc. (N.S.) 10 (1984), no. 2, 177-219, https://doi.org/10.1090/S0273-0979-1984-15237-6, p. 186, §II.A, Theorem (Hasse-Minkowski)

import Mathlib

namespace Gelbart

theorem hasse_minkowski
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ) (hsymm : A.IsSymm) (hdet : A.det ≠ 0) :
    (∃ x : Fin n → ℤ, x ≠ 0 ∧ ∑ i, ∑ j, A i j * x i * x j = 0) ↔
      ((∃ x : Fin n → ℝ, x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℝ) * x i * x j = 0) ∧
        ∀ (p : ℕ) (hp : p.Prime),
          letI : Fact p.Prime := ⟨hp⟩
          ∃ x : Fin n → ℚ_[p], x ≠ 0 ∧ ∑ i, ∑ j, (A i j : ℚ_[p]) * x i * x j = 0) := by sorry

end Gelbart
