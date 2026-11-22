-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanWeightedExponentialTangent
-- name    : Kyprianou.Ch01.mckeanWeightedExponentialTangent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T20:38:01.441734+00:00
-- url     : https://prove2.me/theorems/b8ddd0c6-48e5-4b30-8aab-f7295edbadd5
-- title:
--   Elementary weighted exponential tangent bound for McKean affine support
-- statement:
--   Weighted exponential tangent bound: phi exp(v)+exp(−phi v)≥1+phi for phi>0, by exp(v)≥1+v and exp(−phi v)≥1−phi v. This elementary inequality supplies the global exponential-affine supporting line for the McKean candidate below its exercise boundary and is a direct necessary child of the mckeanAffineExponentialSupportingMajorant theorem.
-- source:
--   Convexity of exp, supporting majorant for Kyprianou (2006) Ch1 McKean verification.

import Mathlib
open Real
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanWeightedExponentialTangent
    (phi v : ℝ) (hphi : 0 < phi) :
    1 + phi ≤ phi * Real.exp v + Real.exp (-phi * v) := by sorry
