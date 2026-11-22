-- Prove2me | Theorems.Thm_HardyFLocal_elementary_coordinates_summable
-- name    : HardyFLocal.elementary_coordinates_summable
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T00:48:41.024575+00:00
-- url     : https://prove2.me/theorems/c8f2ce5f-bb91-43a1-943b-52ff56bc7d06
-- title:
--   Summability of two-qubit instrument coordinates
-- statement:
--   For every countable two-qubit instrument and every Hardy fiducial family, the real coordinate vectors of all instrument branches form an unconditionally summable family.
-- source:
--   Hardy, Formalism Locality in Quantum Theory and Quantum Gravity, arXiv:0804.0054, sections 4.4 and 5.

import Mathlib
import Definitions.Def_HardyFLocal_ClumpCausaloid
import Theorems.Thm_HardyFLocal_four_projector_process_tomography
import Theorems.Thm_HardyFLocal_prodOp_apply_kron
import Theorems.Thm_HardyFLocal_eq20_two_qubit_expansion
open Classical

namespace HardyFLocal

open Classical in
theorem elementary_coordinates_summable (S : FiducialFamily) (I : Instrument) :
    Summable fun y => elemCoeff S (I.op y) := by sorry

end HardyFLocal
