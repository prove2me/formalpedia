-- Prove2me | Theorems.Thm_MatrixAnalytic_Stability_G_structure
-- name    : MatrixAnalytic.Stability.G_structure
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:39.251214+00:00
-- url     : https://prove2.me/theorems/72a2e39b-8e21-4b18-b97e-f51efc04421b
-- title:
--   Theorem 7.2.1 — if A is irreducible, G is irreducible or has the form (7.6) with G₁ irreducible and G_• strictly lower triangular
-- statement:
--   Let $P$ be the transition matrix (6.1) of a homogeneous QBD with blocks $B, A_0, A_1, A_2$ and finitely many phases, assume $P$ is stochastic and irreducible, and assume the phase matrix $A = A_0 + A_1 + A_2$ is irreducible. Let $G$ be the first-passage matrix from $\ell(1)$ to $\ell(0)$. Then either $G$ is irreducible or, after a permutation of its rows and columns,
--   $$G = \begin{bmatrix} G_1 & 0 \\ G_{\bullet 1} & G_\bullet \end{bmatrix}, \tag{7.6}$$
--   where $G_1$ is irreducible and $G_\bullet$ is strictly lower triangular (lower triangular with zero diagonal).
--
--   Thus the chain with transition matrix $G$ has a single irreducible class, possibly with ephemeral states; this is used in the null-recurrent case of the drift criterion.
--
--   **Formalization Note** The permutation is a bijection $\sigma$ from the phases to $\{0, \dots, m-1\}$, and $G_1$ is the block of the phases with $\sigma(i) < k$ for some $1 \le k \le m$. The block form says: $G_{ij} = 0$ when $\sigma(i) < k \le \sigma(j)$; $G_1$ is irreducible; and $G_{ij} = 0$ when $k \le \sigma(i) \le \sigma(j)$. Irreducibility of a nonnegative matrix means that for all $i, j$ some power $t \ge 1$ has a nonzero $(i,j)$ entry. $G$ is defined probabilistically with entries in $[0,\infty]$; only which entries vanish matters here.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 152, Theorem 7.2.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD
import Definitions.Def_MatrixAnalytic_Stability_Passage

open scoped ENNReal

namespace MatrixAnalytic.Stability

/-- Theorem 7.2.1 (p. 152). If the QBD is irreducible, `A = A₀ + A₁ + A₂` is irreducible and the
number of phases is finite, then either the first-passage matrix `G` is irreducible, or after a
simultaneous permutation `σ` of its rows and columns it has the block form (7.6)
`G = [G₁ 0; G_{•1} G_•]`, where `G₁` (the phases with `σ i < k`, `k ≥ 1`) is irreducible and
`G_•` is strictly lower triangular (lower triangular with zero diagonal). -/
theorem G_structure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hA : IrreducibleC (matA A₀ A₁ A₂)) :
    IrreducibleE (matG (qbdP B A₀ A₁ A₂) 0) ∨
      ∃ (σ : ι ≃ Fin (Fintype.card ι)) (k : ℕ), 0 < k ∧ k ≤ Fintype.card ι ∧
        (∀ i j : ι, (σ i : ℕ) < k → k ≤ (σ j : ℕ) → matG (qbdP B A₀ A₁ A₂) 0 i j = 0) ∧
        IrreducibleE (fun a b : {i : ι // (σ i : ℕ) < k} => matG (qbdP B A₀ A₁ A₂) 0 a.1 b.1) ∧
        (∀ i j : ι, k ≤ (σ i : ℕ) → k ≤ (σ j : ℕ) → σ i ≤ σ j →
          matG (qbdP B A₀ A₁ A₂) 0 i j = 0) := by sorry

end MatrixAnalytic.Stability
