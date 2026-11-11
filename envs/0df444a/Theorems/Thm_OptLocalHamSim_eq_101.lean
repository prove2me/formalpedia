-- Prove2me | Theorems.Thm_OptLocalHamSim_eq_101
-- name    : OptLocalHamSim.eq_101
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:32:44.20604+00:00
-- url     : https://prove2.me/theorems/541a1773-9d0d-4f86-914e-7eb2a3e7ff21
-- title:
--   Eq. (101) — $V^\dagger\iota_0-\iota_0U^\dagger=V^\dagger(\iota_0U-V\iota_0)U^\dagger$ and $\|V^\dagger\iota_0-\iota_0U^\dagger\|\le\eta$
-- statement:
--   Let $V$ be a unitary on the full space, $U$ a unitary on the data, and $\iota_0$ the embedding. If $\|V\iota_0-\iota_0U\|\le\eta$, then
--
--   $$
--   V^\dagger\iota_0-\iota_0U^\dagger=V^\dagger(\iota_0U-V\iota_0)U^\dagger,\qquad\bigl\|V^\dagger\iota_0-\iota_0U^\dagger\bigr\|\le\eta .
--   $$
--
--   Inverse block calls therefore keep the full-output error of the forward call.
--
--   Differences from the source:
--   - generalization: the embedding ι₀ → any matrix ι from the data space to the full space; reason: the identity and the bound use only the unitarity of V and U
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), eq. (101), p.36

import Mathlib

open scoped Matrix Matrix.Norms.L2Operator

namespace OptLocalHamSim

/-- **Eq. (101)**, Shen, Wu, Yao, Yuan, Zhang, *Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian
Simulation*, STOC 2027 submission (held version, sha256 44a9768a…), p.36: the hypothesis ‖Vι₀ − ι₀U‖ ≤ η and unitarity give
V†ι₀ − ι₀U† = V†(ι₀U − Vι₀)U†, ‖V†ι₀ − ι₀U†‖ ≤ η.

**Formalization Note** Stated for any unitary `V` on the full space, any unitary `U` on the data, and
any matrix `ι` in place of the embedding `ι₀`. -/
theorem eq_101 {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m m ℂ) (hV : V ∈ Matrix.unitaryGroup m ℂ) (U : Matrix n n ℂ)
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (ι : Matrix m n ℂ) (η : ℝ) (hη : ‖V * ι - ι * U‖ ≤ η) :
    Vᴴ * ι - ι * Uᴴ = Vᴴ * (ι * U - V * ι) * Uᴴ ∧ ‖Vᴴ * ι - ι * Uᴴ‖ ≤ η := by sorry

end OptLocalHamSim
