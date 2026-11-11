-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_eq_13
-- name    : MongeApprox.Sparsify.eq_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:02:01.729206+00:00
-- url     : https://prove2.me/theorems/f7eee6c1-5cf9-4246-b1eb-1381b6618a6a
-- title:
--   (13) — a simple matrix is the quadrant mass of its density, and conversely
-- statement:
--   For a simple $p\times q$ matrix $A$, $A_{ij}=A^\square(Q_{ij})$ for $i\in[0..p)$, $j\in[0..q)$. Conversely, every nonnegative $(p-1)\times(q-1)$ matrix $\mu$ is the density matrix of the simple Monge matrix with entries $\mu(Q_{ij})$.
--
--   Differences from the source:
--   - encoding: p × q matrix with rows/columns indexed by [0..p), [0..q); M□ indexed by [0..p−1) × [0..q−1) → `Matrix (Fin p) (Fin q) ℝ`; `density M i j` a function of naturals that is 0 outside [0..p−1) × [0..q−1); reason: Lean convention; same matrices, and positions outside the density matrix have mass zero as in the paper
--   - encoding: µ(Q_ij) for a (p−1) × (q−1) matrix µ → µ placed on positions [0..p−1) × [0..q−1) of ℤ² (zero elsewhere) and summed over Q_ij with `mass`; reason: positions outside the matrix have mass zero, as in the paper
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), (13), printed p. 36 (PDF 38)

import Mathlib
import Definitions.Def_MongeApprox_Sparsify_Monge
import Definitions.Def_MongeApprox_Sparsify_Quadrant

namespace MongeApprox.Sparsify

/-- (13): for a simple `p × q` matrix `A`, `A_ij = A□(Q_ij)` for `i ∈ [0..p)`, `j ∈ [0..q)`.
Conversely, every nonnegative `(p − 1) × (q − 1)` matrix `µ` is the density matrix of the simple
Monge matrix with entries `µ(Q_ij)` (`µ` placed on positions `[0..p−1) × [0..q−1)` of `ℤ²`). -/
theorem eq_13 {p q : ℕ} :
    (∀ A : Matrix (Fin p) (Fin q) ℝ, IsSimple A →
      ∀ (i : Fin p) (j : Fin q), A i j = mass (densityZ A) (Q (i : ℤ) (j : ℤ))) ∧
    (∀ μ : Matrix (Fin (p - 1)) (Fin (q - 1)) ℝ, (∀ a b, 0 ≤ μ a b) →
      let μZ : ℤ × ℤ → ℝ := fun z =>
        if h : 0 ≤ z.1 ∧ z.1 < ((p - 1 : ℕ) : ℤ) ∧ 0 ≤ z.2 ∧ z.2 < ((q - 1 : ℕ) : ℤ) then
          μ ⟨z.1.toNat, by omega⟩ ⟨z.2.toNat, by omega⟩
        else 0
      let B : Matrix (Fin p) (Fin q) ℝ := fun i j => mass μZ (Q (i : ℤ) (j : ℤ))
      IsSimple B ∧ ∀ (a : Fin (p - 1)) (b : Fin (q - 1)), density B a b = μ a b) := by sorry

end MongeApprox.Sparsify
