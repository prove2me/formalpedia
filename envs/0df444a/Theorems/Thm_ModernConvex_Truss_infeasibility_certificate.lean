-- Prove2me | Theorems.Thm_ModernConvex_Truss_infeasibility_certificate
-- name    : ModernConvex.Truss.infeasibility_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:32.61565+00:00
-- url     : https://prove2.me/theorems/9eecf42a-719e-4e10-9c33-577a58216232
-- title:
--   Proposition 2.4.2 — certificate of infeasibility and almost solvability of a conic inequality
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior and $\mathbf K_*$ its dual cone. Let $A$ be an $m \times n$ matrix with linearly independent columns (Assumption A) and $b \in \mathbb R^m$. Consider the linear vector inequality
--   $$Ax - b \ge_{\mathbf K} 0 \qquad \text{(I)}$$
--   and the system
--   $$\lambda \ge_{\mathbf K_*} 0, \quad A^T\lambda = 0, \quad \lambda^Tb > 0. \qquad \text{(II)}$$
--
--   1. If (II) has a solution, then (I) has no solutions.
--   2. If (II) has no solutions, then (I) is almost solvable: for every $\varepsilon > 0$ there is $b'$ with $\|b' - b\|_2 < \varepsilon$ such that $Ax - b' \ge_{\mathbf K} 0$ is solvable.
--   3. (II) is solvable if and only if (I) is not almost solvable.
--
--   In the truss chapter, item 3 is applied to the conic quadratic inequality (3.4.49) to obtain a dual description of the strict epigraph of the compliance (Lemma 3.4.2).
--
--   **Formalization Note** The cone hypotheses are the book's standing assumption on $\mathbf K$ (p. 46); Assumption A (p. 53) is an explicit hypothesis because Remark 2.4.1 (p. 64) states that the consequences of §2.4.2 were obtained under it. $a \ge_{\mathbf K} b$ means $a - b \in \mathbf K$. This proposition is restated from Lecture 2 because the truss chapter relies on it.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 61–62, Proposition 2.4.2

import Mathlib
import Definitions.Def_ModernConvex_Truss_Compliance

open Matrix

namespace ModernConvex.Truss

/-- Ben-Tal–Nemirovski, Proposition 2.4.2, pp. 61–62, for the linear vector inequality
`(I) : Ax − b ≥_K 0` and the system `(II) : λ ≥_{K∗} 0, Aᵀλ = 0, λᵀb > 0`.
(i) If (II) is solvable, (I) has no solutions. (ii) If (II) has no solutions, (I) is almost
solvable: for every `ε > 0` some `b′` with `‖b′ − b‖₂ < ε` makes `Ax − b′ ≥_K 0` solvable.
(iii) (II) is solvable iff (I) is not almost solvable.
`K` is a good cone (p. 46); Assumption A (p. 53) is in force by Remark 2.4.1 (p. 64). -/
theorem infeasibility_certificate {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) :
    -- (i)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      ¬ ∃ x : Fin n → ℝ, A *ᵥ x - b ∈ K) ∧
    -- (ii)
    ((¬ ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) →
      IsAlmostSolvable K A b) ∧
    -- (iii)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = 0 ∧ 0 < l ⬝ᵥ b) ↔
      ¬ IsAlmostSolvable K A b) := by sorry

end ModernConvex.Truss
