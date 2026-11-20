-- Prove2me | Theorems.Thm_GaoQuantumUnion_operator_bound
-- name    : GaoQuantumUnion.operator_bound
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-19T21:46:06.406041+00:00
-- url     : https://prove2.me/theorems/0b9363fc-fcd5-48ac-b37e-5b485be75164
-- title:
--   Corollary 1 — Operator quantum union bound
-- statement:
--   For arbitrary finite orthogonal projectors and $K=P_{N-1}\cdots P_0$,
--
--   $$K^\dagger K\succeq I-4\sum_i(I-P_i).$$
--
--   The order is Loewner order, encoded by positivity of the difference. There is no state hypothesis or commutativity hypothesis.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Corollary 1, PDF p. 4

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem operator_bound {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ((seqOp P)ᴴ*seqOp P-(1-(4 : ℂ) • ∑ i, (1-P i))).PosSemidef := by sorry
end GaoQuantumUnion
