-- Prove2me | Theorems.Thm_GaoQuantumUnion_theorem1
-- name    : GaoQuantumUnion.theorem1
-- status  : Open
-- author  : @Mrnaiq
-- created : 2026-11-19T21:47:34.280228+00:00
-- url     : https://prove2.me/theorems/ac98c211-673a-4760-aa0c-f1f4cd4d974b
-- title:
--   Theorem 1 — Quantum union bounds for success and conditional disturbance
-- statement:
--   For a density operator and a finite sequence of orthogonal projectors, let $K=P_{N-1}\cdots P_0$, $q=\operatorname{Tr}(K\rho K^\dagger)$ and $E=\sum_i\operatorname{Tr}((I-P_i)\rho)$. The target retains both conclusions of Theorem 1:
--
--   $$q\ge1-4E,\qquad q>0\Longrightarrow D(\rho,q^{-1}K\rho K^\dagger)\le2\sqrt E,$$
--
--   together with $q=1-4E$ exactly when all individual failures vanish. The model is finite dimensional; the trace distance is unhalved. The branch-positivity condition applies only to conditional disturbance, preserving the full unconditional probability statement. The equality assertion is for the probability bound.
-- source:
--   Jingliang Gao, Quantum union bounds for sequential projective measurements, arXiv:1410.5688v2, Physical Review A 92, 052331 (2015), https://doi.org/10.1103/PhysRevA.92.052331; Theorem 1, PDF pp. 3–4, including the equality sentence following (1-b); finite-dimensional matrix specialization

import Definitions.Def_GaoQuantumUnion_Model
open Matrix WildeQIT GaoQuantumUnion
open scoped MatrixOrder ComplexOrder ComplexConjugate
set_option autoImplicit false

namespace GaoQuantumUnion
theorem theorem1 {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ)
    (P : Fin N → Matrix ι ι ℂ) (hP : ∀ i, IsProjector (P i)) :
    1-4*failureSum P ρ ≤ successProb P ρ ∧
    (0 < successProb P ρ → traceDist ρ (postState P ρ) ≤ 2*Real.sqrt (failureSum P ρ)) ∧
    (successProb P ρ=1-4*failureSum P ρ ↔ ∀ i, failureTerm (P i) ρ=0) := by sorry
end GaoQuantumUnion
