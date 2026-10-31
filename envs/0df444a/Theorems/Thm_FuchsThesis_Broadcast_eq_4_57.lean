-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_57
-- name    : FuchsThesis.Broadcast.eq_4_57
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:59.113677+00:00
-- url     : https://prove2.me/theorems/a97b621b-b8cd-4b9f-a099-9ce5a04c0e1f
-- title:
--   Eq. (4.57) — the fidelity is symmetric and unitarily invariant
-- statement:
--   For positive operators $\rho_0, \rho_1$ on a finite-dimensional Hilbert space, let
--
--   $$
--   F(\rho_0,\rho_1) = \mathrm{tr}\sqrt{\rho_0^{1/2}\rho_1\rho_0^{1/2}}
--   $$
--
--   be the fidelity (4.56). Then $F$ is invariant under the interchange $0\leftrightarrow1$ and under the simultaneous transformation $\rho_0\to U\rho_0U^\dagger$, $\rho_1\to U\rho_1U^\dagger$ for any unitary $U$:
--
--   $$
--   F(\rho_1,\rho_0) = F(\rho_0,\rho_1), \qquad F(U\rho_0U^\dagger, U\rho_1U^\dagger) = F(\rho_0,\rho_1).
--   $$
--
--   Unitary invariance is what lets the no-broadcasting proof move the fidelity of $\rho_0\otimes\Sigma\otimes\Upsilon$ and $\rho_1\otimes\Sigma\otimes\Upsilon$ through the interaction unitary $U$ in (4.77).
--
--   Differences from the source:
--   - generalization: density operators → positive semidefinite matrices; reason: trace one is not used; density operators are positive semidefinite, so the statement specializes to the source's.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ → the real part of the trace, square roots by the continuous functional calculus of the real square root; reason: Lean convention; on the positive semidefinite arguments the trace is real and the square root is the positive one, so no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.57) with (4.56), p.115 (PDF p.124)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

open scoped Matrix ComplexOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.57), p.115 (PDF p.124): the fidelity
`F(ρ₀, ρ₁) = tr √(ρ₀^{1/2} ρ₁ ρ₀^{1/2})` (4.56) is invariant under the interchange `0 ↔ 1` and
under `ρ₀ → U ρ₀ U†`, `ρ₁ → U ρ₁ U†` for any unitary `U`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity`, which is (4.56) verbatim with square
roots `cfc Real.sqrt` (the positive square root on positive semidefinite matrices). The states are
positive semidefinite matrices on an arbitrary finite index type; the source states it for density
operators (trace one is not needed). -/
theorem eq_4_57 {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (hρ0 : ρ0.PosSemidef) (hρ1 : ρ1.PosSemidef) (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    QAlgorithms.rootFidelity ρ1 ρ0 = QAlgorithms.rootFidelity ρ0 ρ1 ∧
    QAlgorithms.rootFidelity (U * ρ0 * Uᴴ) (U * ρ1 * Uᴴ) = QAlgorithms.rootFidelity ρ0 ρ1 := by sorry

end FuchsThesis.Broadcast
