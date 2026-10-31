-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_101
-- name    : FuchsThesis.Broadcast.eq_4_101
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:27.907398+00:00
-- url     : https://prove2.me/theorems/4332f615-4f65-4a72-a081-2e2196e08ecf
-- title:
--   Eq. (4.101) — broadcastable invertible states commute (the case proved in the source)
-- statement:
--   Let $\rho_0,\rho_1$ be invertible density operators on an $N$-dimensional Hilbert space. If the set $\{\rho_0,\rho_1\}$ can be broadcast, then $\rho_0$ and $\rho_1$ commute:
--
--   $$
--   [\rho_0,\rho_1] = 0 .
--   $$
--
--   This is the converse half of the no-broadcasting theorem in the case the thesis proves ("To simplify the exposition, we assume that $\rho_0$ and $\rho_1$ are invertible", p.118). The mission's goal states the converse for all density operators.
--
--   Differences from the source:
--   - encoding: invertible density operators → positive definite density matrices; reason: for a positive semidefinite matrix invertibility and positive definiteness are equivalent.
--   - encoding: an auxiliary system $C$ → indices $\{0,\dots,k-1\}$ for some natural number $k$; $N$-dimensional spaces → an arbitrary finite index type; reason: Lean convention; covers every finite dimension and every finite-dimensional auxiliary system.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.82)–(4.103), pp.118–120 (PDF pp.127–129); invertibility assumption p.118 (PDF p.127)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_IsBroadcast

open scoped ComplexOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.80)–(4.103), pp.118–120 (PDF pp.127–129): the converse
part of the no-broadcasting theorem in the case the source proves ("To simplify the exposition, we
assume that ρ0 and ρ1 are invertible", p.118): if invertible density operators `ρ₀, ρ₁` can be
broadcast, they commute, `[ρ₀, ρ₁] = 0` (4.101).

**Formalization Note.** Invertibility of a density matrix is `PosDef`. The general statement,
without invertibility, is part of the mission's goal `no_broadcasting`. -/
theorem eq_4_101 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hρ0inv : ρ0.PosDef) (hρ1inv : ρ1.PosDef) (hbc : IsBroadcast ρ0 ρ1) :
    ρ0 * ρ1 = ρ1 * ρ0 := by sorry

end FuchsThesis.Broadcast
