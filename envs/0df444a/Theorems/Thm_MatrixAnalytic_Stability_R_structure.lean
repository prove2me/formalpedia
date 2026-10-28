-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_R_structure
-- name    : MatrixAnalytic.Stability.R_structure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:35.09698+00:00
-- url     : https://prove2.me/theorems/2d0efa86-0865-43ac-869d-772e5cc3e815
-- title:
--   Theorem 7.2.2 — if A is irreducible, R is irreducible or has the form (7.8) with R₁ irreducible and R_• strictly upper triangular
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, assume $P$ is stochastic and irreducible, and assume the phase matrix $A = A_0 + A_1 + A_2$ is irreducible. Let $R$ be the rate matrix: $R_{ij}$ is the expected number of visits to $(1,j)$, starting from $(0,i)$, before the first return to $\ell(0)$. Then either $R$ is irreducible or, after a permutation of its rows and columns,
--   $$R = \begin{bmatrix} R_1 & R_{1\bullet} \\ 0 & R_\bullet \end{bmatrix}, \tag{7.8}$$
--   where $R_1$ is irreducible and $R_\bullet$ is strictly upper triangular (upper triangular with zero diagonal).
--
--   It is the counterpart of Theorem 7.2.1 for $R$: $R$ has a unique irreducible principal submatrix.
--
--   **Formalization Note** The permutation is a bijection $\sigma$ from the phases to $\{0, \dots, m-1\}$, and $R_1$ is the block of the phases with $\sigma(i) < k$ for some $1 \le k \le m$. The block form says: $R_{ij} = 0$ when $\sigma(j) < k \le \sigma(i)$; $R_1$ is irreducible; and $R_{ij} = 0$ when $k \le \sigma(j) \le \sigma(i)$. Irreducibility of a nonnegative matrix means that for all $i, j$ some power $t \ge 1$ has a nonzero $(i,j)$ entry. $R$ is defined probabilistically with entries in $[0,\infty]$; only which entries vanish matters here.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 154, Theorem 7.2.2

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Theorem 7.2.2 (p. 154). If the QBD is irreducible, `A = A₀ + A₁ + A₂` is irreducible and the
number of phases is finite, then either the rate matrix `R` is irreducible, or after a
simultaneous permutation `σ` of its rows and columns it has the block form (7.8)
`R = [R₁ R_{1•}; 0 R_•]`, where `R₁` (the phases with `σ i < k`, `k ≥ 1`) is irreducible and
`R_•` is strictly upper triangular (upper triangular with zero diagonal). -/
theorem R_structure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂)) :
    IrreducibleE (matR (qbdP B A₀ A₁ A₂)) ∨
      ∃ (σ : ι ≃ Fin (Fintype.card ι)) (k : ℕ), 0 < k ∧ k ≤ Fintype.card ι ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → (σ j : ℕ) < k → matR (qbdP B A₀ A₁ A₂) i j = 0) ∧
        IrreducibleE (fun a b : {i : ι // (σ i : ℕ) < k} => matR (qbdP B A₀ A₁ A₂) a.1 b.1) ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → k ≤ (σ j : ℕ) → σ j ≤ σ i →
          matR (qbdP B A₀ A₁ A₂) i j = 0) := by sorry

end MatrixAnalytic.Stability
