-- Prove2me | Theorems.Thm_MatrixLeeSidford_gradient_matrix_posDef_trace
-- name    : MatrixLeeSidford.gradient_matrix_posDef_trace
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:37:29.473647+00:00
-- url     : https://prove2.me/theorems/f6d55371-426d-48b7-b965-0a5c2ea28915
-- title:
--   p.42 — the gradient matrix satisfies $M_y\succ0$ and $\operatorname{tr}M_y=m$
-- statement:
--   Throughout, $A_1,\dots,A_m,C$ are real symmetric $n\times n$ matrices satisfying the standing assumptions (4.3): $\Omega=\{y:S(y)\succ0\}\neq\emptyset$, the $A_i$ are linearly independent, and $\bigcap_i\ker A_i=\{0\}$.
--
--   Let $s\ge2$ be an integer, $y\in\Omega$, $G_*$ the optimal weight, $W_y=L_y(G_*)^{s-1}$ and
--   $$
--   M_y=\frac12\Big(L_y(G_*)^s+\sum_{i,j}(G_*)_{ij}B_iW_yB_j\Big).
--   $$
--   Then $M_y$ is positive definite and $\operatorname{tr}[M_y]=m$.
--
--   The trace identity is what puts the factor $m$ into the barrier parameter $\nu=\alpha m$.
--
--   Differences from the source:
--   - encoding: Aᵢ, C ∈ Sⁿ, y, h ∈ ℝᵐ → real n×n matrices with IsHermitian hypotheses; y, h ∈ EuclideanSpace ℝ (Fin m); reason: Lean representation of the same objects
--   - generalization: s := 2⌈log(2mn)⌉ (Definition 5.1, fixed for Section 5) → every integer s ≥ 2; reason: the proof does not use the value of s; sParam m n ≥ 2 for m, n ≥ 1, so the statement specializes to the source's
--   - encoding: G_*(y), the unique minimizer of f_y → optWeightAt / optWeight, a chosen minimizer (junk 0 if none exists); reason: by Lemma 4.4 the minimizer exists and is unique under (4.3), so the chosen one is G_*
-- source:
--   Song–Zhang, A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming, STOC 2027 submission (manuscript of October 31, 2026, sha256 7c638b45…412c1), p.42, the claim after Definition 5.5

import Mathlib
import Definitions.Def_MatrixLeeSidford_Mmat
import Definitions.Def_MatrixLeeSidford_dualRegion

open Matrix Filter Topology
open scoped ContDiff Pointwise

namespace MatrixLeeSidford

/-- **The gradient matrix is positive definite with trace `m`** (Song–Zhang, *A Matrix Lee–Sidford Barrier and Faster Semidefinite Programming*, STOC 2027 submission manuscript of October 31, 2026 (sha256 7c638b45…412c1), p.42, the claim after
Definition 5.5; Theorem 2.1(c), p.29): for `y ∈ Ω`, `M_y ≻ 0` and `tr[M_y] = m`.

**Formalization Note** The standing assumptions (4.3) (p.32) are hypotheses: `Aᵢ, C` symmetric, `Ω ≠ ∅`, the `Aᵢ`
linearly independent, `⋂ᵢ ker Aᵢ = {0}`. Stated for every integer `s ≥ 2` (the proof does not use the
value of `s` of Definition 5.1). -/
theorem gradient_matrix_posDef_trace {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian)
    (hΩ : (dualRegion A C).Nonempty) (hlin : LinearIndependent ℝ A)
    (hker : ∀ v : Fin n → ℝ, (∀ i, A i *ᵥ v = 0) → v = 0)
    (s : ℕ) (hs : 2 ≤ s) (y : EuclideanSpace ℝ (Fin m)) (hy : y ∈ dualRegion A C) :
    (Mmat A (slack A C y) s).PosDef ∧ (Mmat A (slack A C y) s).trace = m := by sorry

end MatrixLeeSidford
