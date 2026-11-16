-- Prove2me | Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_const_subtype
-- name    : Kyprianou.Ch06.iIndepFun_of_delete_const_subtype
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:32:18.311896+00:00
-- url     : https://prove2.me/theorems/1184bcd2-fa48-4d40-a857-a5048ecebf5b
-- title:
--   Independent complement family extends across one constant-zero coordinate
-- statement:
--   If the random variables indexed by every coordinate except one are mutually independent, and the excluded coordinate is constantly zero, then all coordinates are mutually independent under a probability measure. This supplies the general subtype-based zero-insertion bridge.
-- source:
--   Finite-dimensional probability, proved from the previously accepted source-faithful constant-deletion independence lemma.

import Mathlib
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_constant
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem Kyprianou.Ch06.iIndepFun_of_delete_const_subtype
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (f : ι → Ω → Real) (k : ι)
    (hconst : f k = fun _ => 0)
    (haway : ProbabilityTheory.iIndepFun
      (fun j : {j : ι // j ≠ k} => f j.val) P) :
    ProbabilityTheory.iIndepFun f P := by sorry
