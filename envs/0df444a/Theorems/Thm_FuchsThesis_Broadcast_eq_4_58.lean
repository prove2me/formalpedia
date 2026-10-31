-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_58
-- name    : FuchsThesis.Broadcast.eq_4_58
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:30.967705+00:00
-- url     : https://prove2.me/theorems/5ba93ccb-2f98-40f1-ada9-16808ca9fe12
-- title:
--   Eq. (4.58) — $F(\rho_0\otimes\sigma_0, \rho_1\otimes\sigma_1) = F(\rho_0,\rho_1)F(\sigma_0,\sigma_1)$
-- statement:
--   Let $\rho_0,\rho_1$ be positive operators on a finite-dimensional Hilbert space and $\sigma_0,\sigma_1$ positive operators on another. The fidelity $F(\rho_0,\rho_1) = \mathrm{tr}\sqrt{\rho_0^{1/2}\rho_1\rho_0^{1/2}}$ of (4.56) is multiplicative over tensor (direct) products:
--
--   $$
--   F(\rho_0\otimes\sigma_0,\; \rho_1\otimes\sigma_1) = F(\rho_0,\rho_1)\,F(\sigma_0,\sigma_1).
--   $$
--
--   In the no-broadcasting proof this gives $F(\rho_0\otimes\Sigma\otimes\Upsilon, \rho_1\otimes\Sigma\otimes\Upsilon) = F(\rho_0,\rho_1)$ in (4.77), and $F(\rho_0\otimes\rho_0,\rho_1\otimes\rho_1) = F(\rho_0,\rho_1)^2$ in the cloning argument (4.81).
--
--   Differences from the source:
--   - generalization: density operators → positive semidefinite matrices; reason: trace one is not used; density operators are positive semidefinite, so the statement specializes to the source's.
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ → the real part of the trace, square roots by the continuous functional calculus; tensor product → Kronecker product indexed by pairs; reason: Lean convention, no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eq. (4.58), p.115 (PDF p.124)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation

open scoped Kronecker ComplexOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eq. (4.58), p.115 (PDF p.124): the fidelity (4.56) is
multiplicative over direct (tensor) products,
`F(ρ₀ ⊗ σ₀, ρ₁ ⊗ σ₁) = F(ρ₀, ρ₁) F(σ₀, σ₁)`.

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56). `ρ₀, ρ₁` live on an arbitrary
finite index type `a`, `σ₀, σ₁` on `b`, and `ρ ⊗ σ` is the Kronecker product indexed by `a × b`.
The operators are positive semidefinite (the source's density operators, without trace one). -/
theorem eq_4_58 {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ0 ρ1 : Matrix a a ℂ) (σ0 σ1 : Matrix b b ℂ)
    (hρ0 : ρ0.PosSemidef) (hρ1 : ρ1.PosSemidef) (hσ0 : σ0.PosSemidef) (hσ1 : σ1.PosSemidef) :
    QAlgorithms.rootFidelity (ρ0 ⊗ₖ σ0) (ρ1 ⊗ₖ σ1) =
      QAlgorithms.rootFidelity ρ0 ρ1 * QAlgorithms.rootFidelity σ0 σ1 := by sorry

end FuchsThesis.Broadcast
