-- Prove2me | Theorems.Thm_IsotropicSpin_eq_14
-- name    : IsotropicSpin.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:25:36.140365+00:00
-- url     : https://prove2.me/theorems/9af76c6f-691c-49fb-9f8d-6f5d2df060e2
-- title:
--   Eq. (14) — $S[\Lambda_1]\ge\log2$
-- statement:
--   Let $\Lambda_1$ be the isotropic spin-1 channel (6) with the matrices (13). For every density matrix $\rho$ on $\mathbb C^3$,
--
--   $$
--   S\big(\Lambda_1(\rho)\big)\ge\log 2 ,
--   $$
--
--   where $S$ is the von Neumann entropy. Equivalently $S[\Lambda_1]\ge\log 2$ for the infimum (1) over density matrices, and a fortiori over pure states. This is the lower half of (10).
--
--   **Formalization Note** $S$ is the published `WHAdditivity.Renyi.vonNeumannEntropy`; a density matrix is positive semidefinite with trace one.
--
--   Differences from the source:
--   - encoding: S[Λ_1] ≥ log 2, a bound on the infimum (1) → log 2 ≤ S(Λ_1(ρ)) for every density matrix ρ; reason: a lower bound on an infimum over a nonempty set is the same as a lower bound on every element; it also bounds the pure-state form of (1)
--   - encoding: log (no base stated) → Real.log, the natural logarithm, inside the von Neumann entropy WHAdditivity.Renyi.vonNeumannEntropy (0 log 0 = 0); reason: Lean convention; every term of the statement scales by the same factor under a change of base
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (14), p.2

import Mathlib
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_IsotropicSpin_spinOne
import Definitions.Def_IsotropicSpin_isotropicChannel

namespace IsotropicSpin

/-- **The lower bound `S[Λ₁] ≥ log 2` (14)**, Alicki, arXiv:quant-ph/0402080v1, eq. (14), p. 2: for
every density matrix `ρ` on `ℂ³`, `S(Λ₁(ρ)) ≥ log 2`.

**Formalization Note** The bound on the infimum `S[Λ₁]` of (1) is stated pointwise for every
density matrix (positive semidefinite, trace one), which covers both forms of (1) since every
`|φ⟩⟨φ|` is a density matrix. `S` is the von Neumann entropy of the published bundle
`WHAdditivity.Renyi` (natural logarithm). -/
theorem eq_14 (ρ : Matrix (Fin 3) (Fin 3) ℂ) (hρ : WHAdditivity.Renyi.IsDensity ρ) :
    Real.log 2 ≤ WHAdditivity.Renyi.vonNeumannEntropy (isotropicChannel 1 spinOne ρ) := by sorry

end IsotropicSpin
