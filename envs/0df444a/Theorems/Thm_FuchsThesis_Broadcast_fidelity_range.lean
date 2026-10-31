-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_fidelity_range
-- name    : FuchsThesis.Broadcast.fidelity_range
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:55:37.680986+00:00
-- url     : https://prove2.me/theorems/2f3b8941-976b-4780-a094-d89c3a360564
-- title:
--   Fidelity ranges in $[0,1]$, $F = 0$ iff orthogonal, $F = 1$ iff $\rho_0 = \rho_1$
-- statement:
--   Let $\rho_0,\rho_1$ be density operators on a finite-dimensional Hilbert space and $F(\rho_0,\rho_1) = \mathrm{tr}\sqrt{\rho_0^{1/2}\rho_1\rho_0^{1/2}}$ their fidelity (4.56). Then
--
--   1. $0 \le F(\rho_0,\rho_1) \le 1$;
--   2. $F(\rho_0,\rho_1) = 0$ if and only if the states are orthogonal, $\rho_0\rho_1 = 0$;
--   3. $F(\rho_0,\rho_1) = 1$ if and only if $\rho_0 = \rho_1$.
--
--   This is what turns the cloning constraint $F = F^2$ of (4.81) into "identical or orthogonal".
--
--   Differences from the source:
--   - encoding: "orthogonal" → $\rho_0\rho_1 = 0$; reason: the source's own meaning of orthogonal states, eq. (4.52).
--   - encoding: the trace $\mathrm{tr}\sqrt{\cdot}$ → the real part of the trace, square roots by the continuous functional calculus; reason: Lean convention, no instance changes.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, p.115 (PDF p.124), after (4.56); orthogonality as in (4.52), p.114

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_WildeQIT_IsDensityOperator

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, p.115 (PDF p.124), after (4.56): the fidelity of two density
operators "ranges between 0 and 1, reaching 0 if and only if the states are orthogonal and reaching
1 if and only if ρ0 = ρ1"; orthogonal means `ρ₀ ρ₁ = 0` (4.52).

**Formalization Note.** `F` is `QAlgorithms.rootFidelity` = (4.56); the states are density
matrices on an arbitrary finite index type. -/
theorem fidelity_range {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1) :
    0 ≤ QAlgorithms.rootFidelity ρ0 ρ1 ∧ QAlgorithms.rootFidelity ρ0 ρ1 ≤ 1 ∧
    (QAlgorithms.rootFidelity ρ0 ρ1 = 0 ↔ ρ0 * ρ1 = 0) ∧
    (QAlgorithms.rootFidelity ρ0 ρ1 = 1 ↔ ρ0 = ρ1) := by sorry

end FuchsThesis.Broadcast
