-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_no_broadcasting
-- name    : FuchsThesis.Broadcast.no_broadcasting
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:28.098429+00:00
-- url     : https://prove2.me/theorems/0beb6e72-fedc-43ad-ae44-0fd6d401f23c
-- title:
--   No-broadcasting theorem — $\{\rho_0,\rho_1\}$ can be broadcast iff $[\rho_0,\rho_1]=0$, cloned iff identical or orthogonal
-- statement:
--   Let $A$ and $B$ be quantum systems, each with an $N$-dimensional Hilbert space, and let $\rho_0,\rho_1$ be density operators on $A$. Physical processes on $AB$ are the maps $E(X) = \mathrm{tr}_C\big(U(X\otimes\Upsilon)U^\dagger\big)$ given by a finite-dimensional auxiliary system $C$, a standard state $\Upsilon$ of $C$ and a unitary $U$ on $ABC$; system $B$ starts in a standard state $\Sigma$. Then:
--
--   1. the set $\{\rho_0,\rho_1\}$ can be broadcast (some process yields states $\tilde\rho_s = E(\rho_s\otimes\Sigma)$ with $\mathrm{tr}_A\tilde\rho_s = \mathrm{tr}_B\tilde\rho_s = \rho_s$ for $s = 0,1$) if and only if $\rho_0$ and $\rho_1$ commute,
--
--   $$
--   \rho_0\rho_1 = \rho_1\rho_0 ;
--   $$
--
--   2. the set $\{\rho_0,\rho_1\}$ is clonable (some process yields $E(\rho_s\otimes\Sigma) = \rho_s\otimes\rho_s$ for $s = 0,1$) if and only if $\rho_0$ and $\rho_1$ are identical or orthogonal,
--
--   $$
--   \rho_0 = \rho_1 \quad\text{or}\quad \rho_0\rho_1 = 0 .
--   $$
--
--   The theorem extends the pure-state no-cloning theorem to mixed states and separates commuting (classical) from noncommuting (quantum) pairs of states: only commuting pairs can be broadcast, even when correlated or entangled joint states are allowed.
--
--   Differences from the source:
--   - encoding: $N$-dimensional Hilbert spaces → matrices indexed by an arbitrary finite type; an auxiliary system $C$ → indices $\{0,\dots,k-1\}$ for some natural number $k$; reason: Lean convention; covers every finite dimension and every finite-dimensional auxiliary system.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3 "Noncommuting Quantum States Cannot Be Broadcast", p.114 (PDF p.123), with (4.52)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_IsBroadcast
import Definitions.Def_FuchsThesis_Broadcast_IsClone

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3 "Noncommuting Quantum States Cannot Be Broadcast", p.114
(PDF p.123), with (4.52): for two density operators `ρ₀, ρ₁` of an `N`-dimensional system,
1. the set `{ρ₀, ρ₁}` can be broadcast if and only if `ρ₀` and `ρ₁` commute;
2. `{ρ₀, ρ₁}` is clonable if and only if `ρ₀` and `ρ₁` are identical or orthogonal, `ρ₀ ρ₁ = 0`.

**Formalization Note.** `N` is the cardinality of the arbitrary finite index type `n`; broadcasting
and cloning are `IsBroadcast` and `IsClone` (eqs. (4.48)–(4.51), any finite auxiliary system). No
invertibility is assumed: the source announces the theorem for all states and proves the
"broadcast ⇒ commute" direction only for invertible ones (p.118). -/
theorem no_broadcasting {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1) :
    (IsBroadcast ρ0 ρ1 ↔ ρ0 * ρ1 = ρ1 * ρ0) ∧
    (IsClone ρ0 ρ1 ↔ (ρ0 = ρ1 ∨ ρ0 * ρ1 = 0)) := by sorry

end FuchsThesis.Broadcast
