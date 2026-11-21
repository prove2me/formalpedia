-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_native_integer_determinant
-- name    : InfoLossLAR.WorstCase.RegevSketch.native_integer_determinant
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-20T15:09:41.388462+00:00
-- url     : https://prove2.me/theorems/9b559d90-888a-447e-9fd9-0b8a13568b62
-- title:
--   Uniform binary polynomial-time determinant of an integer matrix
-- statement:
--   There is one native polynomial-time program on lists of integer rows that returns the exact determinant on every square integer matrix, including the empty matrix. Runtime is measured in the native binary representation. On a ragged list its result is unrestricted.
-- source:
--   Erwin H. Bareiss, Sylvester’s Identity and Multistep Integer-Preserving Gaussian Elimination, Mathematics of Computation 22 (1968), 565–578, https://doi.org/10.1090/S0025-5718-1968-0226829-0. The native program certificate and the bit-size accounting are part of this formulation.

import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false
open OAI.MetricKMedian.Binary.Automatic

namespace InfoLossLAR.WorstCase.RegevSketch

theorem native_integer_determinant :
    ∃ det : List (List ℤ) → ℤ, Poly det ∧
      ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℤ),
        det (List.ofFn fun a => List.ofFn (H a)) = H.det := by
  sorry

end InfoLossLAR.WorstCase.RegevSketch
