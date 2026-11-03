-- Prove2me | Theorems.Thm_IsotropicSpin_eq_17
-- name    : IsotropicSpin.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:26:19.266326+00:00
-- url     : https://prove2.me/theorems/7fd959cf-4590-453e-9a20-97b13b1de292
-- title:
--   Eq. (17) — $\langle\xi,\Omega\xi\rangle\le\tfrac12\|Y^\dagger Y\|$
-- statement:
--   Let $S_1,S_2,S_3$ be the spin-1 matrices (13), let $\phi,\xi\in\mathbb C^3$ be unit vectors, let $\Omega$ be the matrix $\Omega_{kl}=\tfrac12\langle\phi,S_lS_k\phi\rangle$ of (15) for $\Lambda_1$, and let $Y=\sum_k\xi_kS_k$ (18). Then the matrix element $\langle\xi,\Omega\xi\rangle$ is real and
--
--   $$
--   \langle\xi,\Omega\xi\rangle\le\frac12\,\|Y^\dagger Y\|,
--   $$
--
--   where $\|\cdot\|$ is the operator norm. Together with $\|Y^\dagger Y\|=1$ this gives the norm bound (16).
--
--   **Formalization Note** $\langle\xi,v\rangle=\sum_i\overline{\xi_i}v_i$; the norm is the operator norm induced by the Euclidean norm, not the entrywise maximum.
--
--   Differences from the source:
--   - reading: ⟨ξ, Ωξ⟩ ≤ ½‖Y†Y‖ → Im⟨ξ, Ωξ⟩ = 0 and Re⟨ξ, Ωξ⟩ ≤ ½‖Y†Y‖; reason: an inequality between a matrix element and a real number presupposes that the element is real (Ω is Hermitian); both parts are stated
--   - encoding: Ω_kl = ⟨φ, X_l X_k φ⟩ for Λ_1, with X_k the Kraus operators of (6) → omega φ with entries (1/2)⟨φ, S_l S_k φ⟩; reason: X_k = S_k/√(s(s+1)) = S_k/√2 at s = 1, so X_l X_k = (1/2) S_l S_k; same matrix
--   - encoding: operator norm ‖·‖ → the operator norm induced by the Euclidean norm on ℂ³ (scope Matrix.Norms.L2Operator); reason: the page says "operator norm" (p.2, before (16)); this is that norm
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (17), p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_omega
import Definitions.Def_IsotropicSpin_yMat

open scoped Matrix Matrix.Norms.L2Operator

namespace IsotropicSpin

/-- **The matrix-element bound (17)**, Alicki, arXiv:quant-ph/0402080v1, eq. (17), p. 2: for unit
vectors `φ, ξ ∈ ℂ³`, the matrix element `⟨ξ, Ωξ⟩` of the matrix `Ω` of (15) (for `Λ₁`) is real and
`⟨ξ, Ωξ⟩ ≤ ½ ‖Y†Y‖`, where `Y = Σ_k ξ_k S_k` (18).

**Formalization Note** `‖·‖` is the operator norm induced by the Euclidean norm on `ℂ³`
(`Matrix.Norms.L2Operator`), not the entrywise sup norm. `⟨ξ, v⟩ = Σ conj(ξ_i) v_i`. -/
theorem eq_17 (φ ξ : Fin 3 → ℂ) (hφ : WHAdditivity.Renyi.IsUnitVector φ)
    (hξ : WHAdditivity.Renyi.IsUnitVector ξ) :
    (star ξ ⬝ᵥ (omega φ *ᵥ ξ)).im = 0 ∧
      (star ξ ⬝ᵥ (omega φ *ᵥ ξ)).re ≤ 1 / 2 * ‖(yMat ξ)ᴴ * yMat ξ‖ := by sorry

end IsotropicSpin
