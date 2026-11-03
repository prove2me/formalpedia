-- Prove2me | Theorems.Thm_IsotropicSpin_eq_16
-- name    : IsotropicSpin.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:16.101435+00:00
-- url     : https://prove2.me/theorems/dc174980-1bb6-49e5-86c1-f02de7b952fa
-- title:
--   Eq. (16) — $\Omega\succeq0$, $\operatorname{tr}\Omega=1$, $\|\Omega\|\le\tfrac12$ (corrected: positive semidefinite, not definite)
-- statement:
--   Let $S_1,S_2,S_3$ be the spin-1 matrices (13) and $\phi\in\mathbb C^3$ a unit vector, and let $\Omega$ be the matrix $\Omega_{kl}=\tfrac12\langle\phi,S_lS_k\phi\rangle$ of (15) for $\Lambda_1$. Then $\Omega$ is positive semidefinite, $\operatorname{tr}\Omega=1$, and
--
--   $$
--   \|\Omega\|\le\frac12 ,
--   $$
--
--   where $\|\cdot\|$ is the operator norm. A density matrix with all eigenvalues at most $1/2$ has entropy at least $\log 2$, so by (15) this gives the bound (14) on pure inputs.
--
--   **Formalization Note** The norm is the operator norm induced by the Euclidean norm on $\mathbb C^3$.
--
--   Differences from the source:
--   - correction: Ω is a 3×3 positively defined matrix → Ω is positive semidefinite (Matrix.PosSemidef); reason: Ω is singular for every unit φ: at φ = |+1⟩, Λ_1(|φ⟩⟨φ|) = diag(1/2, 1/2, 0), so by (15) and tr Ω = 1 the spectrum of Ω is (1/2, 1/2, 0); positive definiteness is false, semidefiniteness is what the proof uses
--   - encoding: Ω_kl = ⟨φ, X_l X_k φ⟩ for Λ_1, with X_k the Kraus operators of (6) → omega φ with entries (1/2)⟨φ, S_l S_k φ⟩; reason: X_k = S_k/√(s(s+1)) = S_k/√2 at s = 1, so X_l X_k = (1/2) S_l S_k; same matrix
--   - encoding: operator norm ‖·‖ → the operator norm induced by the Euclidean norm on ℂ³ (scope Matrix.Norms.L2Operator); reason: the page says "operator norm" (p.2, before (16)); this is that norm
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (16) and the sentence before it, p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_omega

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace IsotropicSpin

/-- **The operator-norm bound on `Ω` (16)**, Alicki, arXiv:quant-ph/0402080v1, eq. (16) and the
sentence before it, p. 2: for every unit vector `φ ∈ ℂ³`, the matrix `Ω` of (15) (for `Λ₁`) is a
positive semidefinite `3 × 3` matrix with trace one, and its operator norm satisfies `‖Ω‖ ≤ 1/2`.

**Formalization Note** Corrected: the page's "positively defined" (positive definite) is false
for every unit `φ`, and the statement says positive semidefinite. At `φ = |+1⟩`,
`Λ₁(|φ⟩⟨φ|) = diag(1/2, 1/2, 0)`, and `Ω` has the same nonzero spectrum by (15) with trace one,
so its spectrum is `(1/2, 1/2, 0)`. `‖·‖` is the operator norm
induced by the Euclidean norm (`Matrix.Norms.L2Operator`). -/
theorem eq_16 (φ : Fin 3 → ℂ) (hφ : WHAdditivity.Renyi.IsUnitVector φ) :
    (omega φ).PosSemidef ∧ (omega φ).trace = 1 ∧ ‖omega φ‖ ≤ 1 / 2 := by sorry

end IsotropicSpin
