-- Prove2me | Theorems.Thm_MatrixAnalytic_Nonhomogeneous_recurrent_iff_G_stochastic
-- name    : MatrixAnalytic.Nonhomogeneous.recurrent_iff_G_stochastic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:47:50.709343+00:00
-- url     : https://prove2.me/theorems/50ad3a03-2d62-48e2-9431-c87b6ef58e2c
-- title:
--   Theorem 12.1.5 — with finitely many phases in each level, recurrent iff G⁽¹⁾ is stochastic
-- statement:
--   Let $P$ be the transition matrix (12.1) of a nonhomogeneous QBD that is stochastic and irreducible, and suppose that every level contains finitely many phases, and at least one. Let $G^{(1)}$ be the matrix of first passage probabilities from $\ell(1)$ to $\ell(0)$. Then the QBD is recurrent if and only if $G^{(1)}$ is stochastic:
--   $$\text{every state is recurrent} \iff \sum_{j}G^{(1)}_{ij} = 1\ \text{ for every phase } i \text{ of level } 1.$$
--
--   This is the level-dependent counterpart of the recurrence criterion for homogeneous QBDs (Theorem 7.1.1); unlike the homogeneous case, no explicit drift condition on the blocks is available in general.
--
--   **Formalization Note** $G^{(1)}$ is `matG P 0`, with entries in $[0,\infty]$ (they are probabilities, hence at most one). "Finitely many phases" is a `Fintype` instance on every level.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 262, Theorem 12.1.5

import Mathlib
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Chain
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_QBD
import Definitions.Def_MatrixAnalytic_Nonhomogeneous_Passage

open scoped ENNReal

namespace MatrixAnalytic.Nonhomogeneous

/-- Theorem 12.1.5 (p. 262). If every level of the irreducible nonhomogeneous QBD (12.1)
contains finitely many phases, then the QBD is recurrent (every state is recurrent) if and only
if `G^{(1)} = matG P 0` is stochastic, i.e. each of its rows sums to `1`. -/
theorem recurrent_iff_G_stochastic {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    [∀ n, DecidableEq (ι n)] [∀ n, Nonempty (ι n)]
    (A₀ : (n : ℕ) → ι n → ι (n + 1) → ℝ) (A₁ : (n : ℕ) → ι n → ι n → ℝ)
    (A₂ : (m : ℕ) → ι (m + 1) → ι m → ℝ) (P : (Σ n, ι n) → (Σ n, ι n) → ℝ)
    (hPdef : P = ndqbdP A₀ A₁ A₂)
    (hP : IsStochasticC P) (hirr : IrreducibleC P) :
    (∀ x : Σ n, ι n, Recurrent P x) ↔ ∀ i : ι 1, ∑ j : ι 0, matG P 0 i j = 1 := by sorry

end MatrixAnalytic.Nonhomogeneous
