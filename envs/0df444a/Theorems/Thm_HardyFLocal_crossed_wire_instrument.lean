-- Prove2me | Theorems.Thm_HardyFLocal_crossed_wire_instrument
-- name    : HardyFLocal.crossed_wire_instrument
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T01:05:44.811069+00:00
-- url     : https://prove2.me/theorems/d321b511-5fe7-4533-9a29-91148e31e46c
-- title:
--   One lattice instrument implements independent measurement and reset on both crossing wires
-- statement:
--   At a crossing, independently specified single-qubit projective measurements and pure state preparations on both wires are simultaneously realized by outcome zero of one allowed lattice instrument. Its superoperator is exactly the product of the two required single-qubit maps.
-- source:
--   Hardy, arXiv:0804.0054, section 5, exterior preparations for process tomography.

import Mathlib
import Definitions.Def_HardyFLocal_Lattice
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
import Theorems.Thm_HardyFLocal_projective_measure_prepare_instrument
open scoped Kronecker Matrix
open Classical

namespace HardyFLocal

open Classical in
theorem crossed_wire_instrument (P Q R T : Matrix (Fin 2) (Fin 2) ℂ)
    (hp : P.IsHermitian) (hq : Q.IsHermitian) (hr : R.IsHermitian) (ht : T.IsHermitian)
    (ep : P * P = P) (eq : Q * Q = Q) (er : R * R = R) (et : T * T = T)
    (tr : R.trace = 1) (tt : T.trace = 1) :
    ∃ (I : Instrument) (F G : Op (Fin 2)), I.op 0 = prodOp F G ∧
      (∀ A, F A = (P * A).trace • R) ∧ (∀ B, G B = (Q * B).trace • T) := by sorry

end HardyFLocal
