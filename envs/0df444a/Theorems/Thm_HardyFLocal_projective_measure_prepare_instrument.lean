-- Prove2me | Theorems.Thm_HardyFLocal_projective_measure_prepare_instrument
-- name    : HardyFLocal.projective_measure_prepare_instrument
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:34:06.411699+00:00
-- url     : https://prove2.me/theorems/a03d31af-abc6-4513-a451-30389e103250
-- title:
--   A two-qubit instrument can measure a projector and prepare the next state in the same box
-- statement:
--   Let $P$ be a Hermitian projection on two qubits, and let $R$ be a Hermitian projection of trace one on the same space. There exists a lattice instrument with only two nonzero candidate branches. On a complex input matrix $A$, its outcome maps satisfy
--   $$I_0(A)=\operatorname{Tr}(PA)R,\qquad I_1(A)=\operatorname{Tr}((1-P)A)R.$$
--   All later outcomes have zero map. The instrument implements a selected projective effect and prepares an independently specified pure state at a single exterior vertex.
-- source:
--   Supporting construction for the interior fiduciality milestone of the Lean formalization of Lucien Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, section 5. https://arxiv.org/abs/0804.0054

import Definitions.Def_HardyFLocal_Instrument
open scoped Matrix ComplexOrder

namespace HardyFLocal

theorem projective_measure_prepare_instrument
    (P R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hp : P.IsHermitian) (hr : R.IsHermitian) (pp : P * P = P) (rr : R * R = R)
    (unitTrace : R.trace = 1) :
    ∃ I : Instrument,
      (∀ A, I.op 0 A = (P * A).trace • R) ∧
      (∀ A, I.op 1 A = ((1 - P) * A).trace • R) ∧
      (∀ n : ℕ, I.op (n + 2) = 0) := by sorry

end HardyFLocal
