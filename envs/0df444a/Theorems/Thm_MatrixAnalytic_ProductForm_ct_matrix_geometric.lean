-- Prove2me | Theorems.Thm_MatrixAnalytic_ProductForm_ct_matrix_geometric
-- name    : MatrixAnalytic.ProductForm.ct_matrix_geometric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:27.887167+00:00
-- url     : https://prove2.me/theorems/6e458f83-8f11-40b5-9106-e0075850ace6
-- title:
--   Theorem 6.4.1 — π_n = π₀Rⁿ for a positive recurrent continuous-time QBD, with R = A₀N
-- statement:
--   Let $Q$ be the generator of a continuous-time QBD with blocks $B, A_0, A_1, A_2$ on a countable (possibly infinite) set of phases: $A_0$ and $A_2$ nonnegative, $A_1$ and $B$ with nonnegative off-diagonal and strictly negative diagonal entries, and zero row sums. Assume that the process is irreducible, regular and positive recurrent, and let $\pi=(\pi_0,\pi_1,\dots)$, partitioned by levels, be a stationary probability vector ($\pi Q=0$, $\pi\mathbf 1=1$, $\pi\ge 0$).
--
--   Then there are nonnegative real (in particular finite) matrices $R$ and $N$ such that
--
--   - for every $n\ge 0$, $R$ records the rate of sojourn in the states of $\ell(n+1)$ per unit of the local time of $\ell(n)$;
--   - for every $n\ge 1$, $N$ records the expected sojourn time in the states of $\ell(n)$, starting from $\ell(n)$, before the first visit to $\ell(n-1)$;
--   - $R=A_0N$; and
--   $$\pi_n=\pi_0R^n\qquad\text{for } n\ge 0 .$$
--
--   This is the continuous-time matrix-geometric property: the stationary distribution of a QBD is determined by its boundary vector $\pi_0$ and the single matrix $R$. In Chapter 15 it is the step "$\pi_n=\pi_{n-1}R$" of the proof of Theorem 15.1.1.
--
--   **Formalization Note** $R$ and $N$ are the probabilistic matrices of the file `QBD` (expected sojourn times through the jump chain), shown here to be finite, independent of the level and related by $R=A_0N$. The products $A_0N$, $\pi_0R^n$ are computed in $[0,+\infty]$, where they are always defined; the identity $\pi_n=\pi_0R^n$ is stated entrywise there. The book proves this result by reference to Theorem 5.5.1 and Proposition 5.5.4; its hypotheses (the form (6.19), irreducibility, regularity, positive recurrence) are those of the page.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 142, Theorem 6.4.1

import Mathlib
import Definitions.Def_MatrixAnalytic_ProductForm_Chain
import Definitions.Def_MatrixAnalytic_ProductForm_QBD

open scoped ENNReal

namespace MatrixAnalytic.ProductForm

/-- Theorem 6.4.1 (p. 142). For a continuous-time QBD with generator (6.19) that is irreducible,
regular and positive recurrent, with stationary distribution `π`, there are finite nonnegative
matrices `R` and `N` such that `R` is the rate of sojourn in `ℓ(n + 1)` per unit local time of
`ℓ(n)` for every `n ≥ 0`, `N` is the expected sojourn time in `ℓ(n)` from `ℓ(n)` before the first
visit to `ℓ(n − 1)` for every `n ≥ 1`, `R = A₀N`, and `π_n = π₀Rⁿ` for `n ≥ 0`. Products of
nonnegative matrices are computed in `ℝ≥0∞`. -/
theorem ct_matrix_geometric {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ) (π : ℕ × ι → ℝ)
    (hQ : IsGeneratorC (qbdQ B A₀ A₁ A₂))
    (hirr : IrreducibleCT (qbdQ B A₀ A₁ A₂))
    (hreg : RegularCT (qbdQ B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrentCT (qbdQ B A₀ A₁ A₂) x)
    (hπ : IsStationaryCT (qbdQ B A₀ A₁ A₂) π) :
    ∃ R N : ι → ι → ℝ, (∀ i j, 0 ≤ R i j) ∧ (∀ i j, 0 ≤ N i j) ∧
      (∀ n : ℕ, rateR (qbdQ B A₀ A₁ A₂) n = ennMat R) ∧
      (∀ n : ℕ, 1 ≤ n → matNct (qbdQ B A₀ A₁ A₂) n = ennMat N) ∧
      matMulE (ennMat A₀) (ennMat N) = ennMat R ∧
      (∀ n : ℕ, ∀ j : ι, ENNReal.ofReal (π (n, j)) =
        vecMulE (fun i => ENNReal.ofReal (π (0, i))) (matPowE (ennMat R) n) j) := by sorry

end MatrixAnalytic.ProductForm
