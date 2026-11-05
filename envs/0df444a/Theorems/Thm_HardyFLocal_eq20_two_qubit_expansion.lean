-- Prove2me | Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
-- name    : HardyFLocal.eq20_two_qubit_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:39:10.718729+00:00
-- url     : https://prove2.me/theorems/37369875-0a28-415d-a646-c21518c9996b
-- title:
--   Eq. (20), p.12 — expansion of a two-qubit superoperator
-- statement:
--   Let $\$_k$ be a fiducial family. Every completely positive two-qubit map is Hermiticity-preserving, and every Hermiticity-preserving two-qubit map $\Phi$ satisfies
--   $$\Phi=\sum_{k_uk_v\in\Omega^2\times\Omega^2}\Lambda^{k_uk_v}_{\Phi}\,\$_{k_u}\otimes\$_{k_v},$$
--   with $\Lambda_\Phi$ the elementary table and these real coefficients unique.
--
--   This is the first level of the compression: the 256 labels at a vertex suffice, and the table is well defined.
--
--   Differences from the source:
--   - generalization: "a general superoperator on two qubits" → every Hermiticity-preserving two-qubit map, with the conclusion that every completely positive one is such a map; reason: superoperators of the paper are completely positive (R4), hence Hermiticity-preserving; the statement for them is the instance
--   - reading: a "fiducial spanning set of superoperators", with Λ in "a real vector space" (p.9) → a basis over ℝ of the Hermiticity-preserving one-qubit maps; reason: real coefficients are what p.9 requires, and they exist for Hermiticity-preserving maps
--   - encoding: labels run from 1, and the first element of Ω² is 1 → labels are 0-based, and the first element of Ω² = Fin 16 is 0; reason: Lean convention; same instances
-- source:
--   L. Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054v1, §5, eq. (20), p.12

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
import Definitions.Def_HardyFLocal_FiducialFamily

set_option autoImplicit false

namespace HardyFLocal

/-- **Eq. (20): expansion of a two-qubit superoperator**, Hardy, arXiv:0804.0054v1, §5, eq. (20),
p.12 ("In quantum theory we can write a general superoperator on two qubits such as this as a sum of
the tensor product of a fiducial set of superoperators acting on each qubit separately").

Every completely positive two-qubit map is Hermiticity-preserving, and every Hermiticity-preserving
two-qubit map `Φ` is `Σ_{a,b} Λ^{ab}_Φ $_a ⊗ $_b` with `Λ = elemCoeff S Φ`, and these real
coefficients are unique. -/
theorem eq20_two_qubit_expansion (S : FiducialFamily) :
    (∀ Φ : Op (Fin 2 × Fin 2), IsCP Φ → Φ ∈ hpMaps (Fin 2 × Fin 2)) ∧
    ∀ Φ ∈ hpMaps (Fin 2 × Fin 2),
      Φ = ∑ p : Ω × Ω, elemCoeff S Φ p • prodOp (S.map p.1) (S.map p.2) ∧
      ∀ c : Ω × Ω → ℝ, Φ = ∑ p : Ω × Ω, c p • prodOp (S.map p.1) (S.map p.2) →
        c = elemCoeff S Φ := by sorry

end HardyFLocal
