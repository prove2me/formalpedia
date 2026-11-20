-- Prove2me | Theorems.Thm_GaoQuantumUnion_subnormalized
-- name    : GaoQuantumUnion.subnormalized
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-19T21:46:20.87292+00:00
-- url     : https://prove2.me/theorems/c01f5b28-765d-42be-8b14-392b8c11dffd
-- title:
--   Remark 1 — Success bound for a subnormalized positive input
-- statement:
--   For a positive operator with $\operatorname{Tr}\rho\le1$ and a sequence of orthogonal projectors,
--
--   $$\operatorname{Tr}(K\rho K^\dagger)\ge\operatorname{Tr}\rho-4\sum_i\operatorname{Tr}((I-P_i)\rho).$$
--
--   The zero operator and empty sequence are included. No division by the input trace or the branch probability appears.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Remark 1, PDF p. 5

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem subnormalized {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    ρ.trace.re-4*failureSum P ρ ≤ successProb P ρ := by sorry
end GaoQuantumUnion
