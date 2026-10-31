-- Prove2me | Theorems.Thm_FuchsThesis_Broadcast_eq_4_97
-- name    : FuchsThesis.Broadcast.eq_4_97
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:27.34576+00:00
-- url     : https://prove2.me/theorems/991a419a-7020-4c14-aa65-e2f2544df59e
-- title:
--   Eqs. (4.95)–(4.97) — $\rho_0 = G\rho_1G$ has the unique positive solution $G = M$
-- statement:
--   Let $\rho_0,\rho_1$ be density operators on a finite-dimensional Hilbert space with $\rho_1$ invertible, and let
--
--   $$
--   M = \rho_1^{-1/2}\sqrt{\rho_1^{1/2}\rho_0\,\rho_1^{1/2}}\;\rho_1^{-1/2}
--   $$
--
--   be the operator of (4.72). Then the equation
--
--   $$
--   \rho_0 = G\rho_1G
--   $$
--
--   has a unique positive solution $G$, namely $M$: $M$ is positive, $M\rho_1M = \rho_0$, and every positive operator $G$ with $G\rho_1G = \rho_0$ equals $M$.
--
--   In the no-broadcasting proof this identifies the two operators $G$ and $H$ of (4.87)–(4.88) with $M$ (4.97), which is the step that makes the conditions (4.89), (4.90) on the two marginals comparable.
--
--   Differences from the source:
--   - generalization: $\rho_0$ invertible (the standing assumption of this part of the proof, p.118) → $\rho_0$ any density operator; reason: the uniqueness argument (4.96) uses only the invertibility of $\rho_1$; the source's case is included.
--   - reading: "these equations have a unique positive solution, namely the operator $M$" → $M$ is positive semidefinite and solves the equation, and every positive semidefinite solution equals $M$; reason: existence and uniqueness are both asserted; "positive" is the source's "Hermitian operator with nonnegative eigenvalues" (p.115).
--   - encoding: $\rho_1$ invertible → $\rho_1$ positive definite; reason: for a positive semidefinite matrix the two are equivalent.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §4.3, eqs. (4.95)–(4.97), p.119 (PDF p.128), with (4.72), p.116 (PDF p.125)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Broadcast_operatorM

open scoped ComplexOrder

namespace FuchsThesis.Broadcast

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §4.3, eqs. (4.95)–(4.97), p.119 (PDF p.128), with `M` of (4.72), p.116:
for invertible `ρ₁`, the equation `ρ₀ = G ρ₁ G` has a unique positive solution `G`, namely `M`.
That is, `M` is positive and `M ρ₁ M = ρ₀`, and every positive `G` with `G ρ₁ G = ρ₀` equals `M`.

**Formalization Note.** "Positive operator" is the source's "Hermitian operator with nonnegative
eigenvalues" (p.115), i.e. `PosSemidef`. Invertibility of `ρ₁` is `ρ₁.PosDef` (a positive
semidefinite invertible matrix). The source also assumes `ρ₀` invertible in this part of the
proof; the uniqueness does not use it and it is not assumed. -/
theorem eq_4_97 {n : Type} [Fintype n] [DecidableEq n] (ρ0 ρ1 : Matrix n n ℂ)
    (hρ0 : WildeQIT.IsDensityOperator ρ0) (hρ1 : WildeQIT.IsDensityOperator ρ1)
    (hρ1inv : ρ1.PosDef) :
    (operatorM ρ0 ρ1).PosSemidef ∧ operatorM ρ0 ρ1 * ρ1 * operatorM ρ0 ρ1 = ρ0 ∧
    ∀ G : Matrix n n ℂ, G.PosSemidef → G * ρ1 * G = ρ0 → G = operatorM ρ0 ρ1 := by sorry

end FuchsThesis.Broadcast
