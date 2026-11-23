-- Prove2me | Theorems.Thm_GaoQuantumUnion_probability
-- name    : GaoQuantumUnion.probability
-- status  : Proved
-- author  : @Mrnaiq
-- created : 2026-11-19T21:45:47.967865+00:00
-- url     : https://prove2.me/theorems/f5044c68-2fc2-470f-bfcd-277416b9b1d9
-- title:
--   Theorem 1(b) — Joint success probability and its equality condition
-- statement:
--   For a density operator and an ordered sequence of orthogonal projectors,
--
--   $$q\ge1-4E,\qquad q=1-4E\iff\forall i,\ \varepsilon_i=0,$$
--
--   where $\varepsilon_i=\operatorname{Tr}((I-P_i)\rho)$ and $E$ is their sum. This is unconditional in $q$: a zero-probability branch remains an instance. The equality clause belongs to the probability estimate.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Theorem 1(1-b), PDF pp. 3–4; proof on pp. 8–10

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem probability {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    1-4*failureSum P ρ ≤ successProb P ρ ∧
    (successProb P ρ=1-4*failureSum P ρ ↔ ∀ i, failureTerm (P i) ρ=0) := by sorry
end GaoQuantumUnion
