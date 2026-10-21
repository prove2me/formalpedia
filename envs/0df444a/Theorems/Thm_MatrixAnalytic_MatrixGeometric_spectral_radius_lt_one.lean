-- Prove2me | Theorems.Thm_MatrixAnalytic_MatrixGeometric_spectral_radius_lt_one
-- name    : MatrixAnalytic.MatrixGeometric.spectral_radius_lt_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:44:10.30668+00:00
-- url     : https://prove2.me/theorems/bf0d47ac-6cf5-4aa9-b62a-9614caceb5de
-- title:
--   Corollary 6.2.4 — for finitely many phases, sp(R) < 1
-- statement:
--   Consider an irreducible, positive recurrent homogeneous QBD with blocks $B,A_0,A_1,A_2$ and a **finite** set of $m$ phases. Let $R$ be the $m\times m$ matrix whose $(i,j)$ entry is the expected number of visits to $(1,j)$, starting from $(0,i)$, before a return to $\ell(0)$. Then every entry of $R$ is finite and
--   $$\operatorname{sp}(R)<1,$$
--   where $\operatorname{sp}(R)$ is the spectral radius, the largest modulus of a complex eigenvalue of $R$.
--
--   This is what makes the matrix-geometric distribution $\pi_n=\pi_0R^n$ summable and allows $(I-R)^{-1}$ to be an honest matrix inverse.
--
--   **Formalization Note** $R$ is taken at level $0$; by Theorem 6.2.1 it is the same at every level. Its entries, a priori in $[0,+\infty]$, are asserted finite and then read as real numbers; the spectral radius is Mathlib's `spectralRadius ℂ` of the matrix viewed over $\mathbb C$. Aperiodicity is not used and is omitted.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 133, Corollary 6.2.4

import Mathlib
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Chain
import Definitions.Def_MatrixAnalytic_MatrixGeometric_QBD
import Definitions.Def_MatrixAnalytic_MatrixGeometric_Passage

open scoped ENNReal

namespace MatrixAnalytic.MatrixGeometric

/-- Corollary 6.2.4 (p. 133). If the QBD is positive recurrent and the number `m` of phases is
finite, the matrix `R` of Theorem 6.2.1 (the expected numbers of visits to `ℓ(1)` from `ℓ(0)`
before a return to `ℓ(0)`) has finite entries and spectral radius strictly less than `1`. The
spectral radius is taken over `ℂ`. -/
theorem spectral_radius_lt_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂))
    (hpos : ∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) :
    (∀ i j, matR (qbdP B A₀ A₁ A₂) 0 i j ≠ ⊤) ∧
      spectralRadius ℂ
        (Matrix.of fun i j => (((matR (qbdP B A₀ A₁ A₂) 0 i j).toReal : ℝ) : ℂ)) < 1 := by sorry

end MatrixAnalytic.MatrixGeometric
