-- Prove2me | Theorems.Thm_ModernConvex_ConicDuality_scalar_consequence
-- name    : ModernConvex.ConicDuality.scalar_consequence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:32:40.933834+00:00
-- url     : https://prove2.me/theorems/f9878e8a-3a2a-41cc-8278-d4798bbdcd25
-- title:
--   Proposition 2.4.3 — when a scalar linear inequality is a consequence of a conic one
-- statement:
--   Let $\mathbf K \subset \mathbb R^m$ be a pointed closed convex cone with nonempty interior, $A$ an $m\times n$ matrix with linearly independent columns (Assumption A), $b \in \mathbb R^m$, $c \in \mathbb R^n$ and $d \in \mathbb R$. Consider the linear vector inequality and the scalar inequality
--   $$\text{(V)}\quad Ax \ge_{\mathbf K} b, \qquad\qquad \text{(S)}\quad c^Tx \ge d.$$
--   (S) is a **consequence** of (V) if every $x$ satisfying (V) satisfies (S).
--
--   1. If (S) can be obtained from (V) and the trivial inequality $1 \ge 0$ by admissible aggregation, i.e. there is a weight vector $\lambda \ge_{\mathbf K_*} 0$ with $A^T\lambda = c$ and $\lambda^Tb \ge d$, then (S) is a consequence of (V).
--   2. If (V) is strictly feasible ($Ax - b \in \operatorname{int}\mathbf K$ for some $x$) and (S) is a consequence of (V), then (S) can be obtained from (V) by an admissible aggregation.
--
--   This is the conic version of the inhomogeneous Farkas lemma; the word "strictly" in item 2 is what distinguishes it from the LP case.
--
--   **Formalization Note** The book's Remark 2.4.1 (p. 64) states that the results of §2.4.2 are obtained under Assumption A, so full column rank of $A$ is a hypothesis, as are the cone conditions of p. 46.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 63, Proposition 2.4.3

import Mathlib
import Definitions.Def_ModernConvex_ConicDuality_ConicProblem

open Matrix

namespace ModernConvex.ConicDuality

/-- Ben-Tal–Nemirovski, Proposition 2.4.3, p. 63, for the linear vector inequality
`(V) : Ax ≥_K b` and the scalar inequality `(S) : cᵀx ≥ d`; "(S) is a consequence of (V)" means
every solution of (V) satisfies (S).
(i) If `λ ≥_{K∗} 0`, `Aᵀλ = c`, `λᵀb ≥ d` for some `λ` (admissible aggregation), then (S) is a
consequence of (V). (ii) If (V) is strictly feasible and (S) is a consequence of (V), then (S) can
be obtained from (V) by an admissible aggregation.
`K` is a good cone (p. 46); Assumption A (p. 53) is in force by Remark 2.4.1 (p. 64). -/
theorem scalar_consequence {m n : ℕ} (K : Set (Fin m → ℝ)) (hK : IsGoodCone K)
    (A : Matrix (Fin m) (Fin n) ℝ) (hA : AssumptionA A) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (d : ℝ) :
    -- (i)
    ((∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = c ∧ d ≤ l ⬝ᵥ b) →
      ∀ x : Fin n → ℝ, A *ᵥ x - b ∈ K → d ≤ c ⬝ᵥ x) ∧
    -- (ii)
    ((∃ x : Fin n → ℝ, A *ᵥ x - b ∈ interior K) →
      (∀ x : Fin n → ℝ, A *ᵥ x - b ∈ K → d ≤ c ⬝ᵥ x) →
      ∃ l : Fin m → ℝ, l ∈ dualCone K ∧ Aᵀ *ᵥ l = c ∧ d ≤ l ⬝ᵥ b) := by sorry

end ModernConvex.ConicDuality
