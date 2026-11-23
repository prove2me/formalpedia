-- Prove2me | Theorems.Thm_GaoQuantumUnion_disturbance
-- name    : GaoQuantumUnion.disturbance
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-19T21:45:28.258621+00:00
-- url     : https://prove2.me/theorems/0b170080-caf5-4e0c-992e-390564aae85d
-- title:
--   Theorem 1(a) — Disturbance of the normalized sequential output
-- statement:
--   For a density operator and any finite ordered family of orthogonal projectors, let $q$ be the probability that every designated outcome occurs, and $E=\sum_i\operatorname{Tr}((I-P_i)\rho)$. If $q>0$, the normalized output satisfies
--
--   $$D(\rho,\rho_N)\le2\sqrt E.$$
--
--   No commutativity, full-rank, or positive-marginal-error assumption is imposed. The empty sequence is included.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Theorem 1(1-a), PDF p. 3; mixed-state proof on p. 8

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem disturbance {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) (hq : 0 < successProb P ρ) :
    traceDist ρ (postState P ρ) ≤ 2*Real.sqrt (failureSum P ρ) := by sorry
end GaoQuantumUnion
