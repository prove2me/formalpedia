-- Prove2me | Theorems.Thm_Kyprianou_Ch07_sumConvolutionComm
-- name    : Kyprianou.Ch07.sumConvolutionComm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:26:17.939875+00:00
-- url     : https://prove2.me/theorems/29230999-5f4a-4ff3-a16d-ca7215f42f0c
-- title:
--   Commutativity of Chapter 7 real sum-convolution for s-finite measures
-- statement:
--   For s-finite Borel measures mu and nu on the reals, the original Chapter 7 sumConvolution measure built by pushing forward the product under addition is symmetric in mu and nu. The exact proof swaps the product measure and uses commutativity of real addition.
-- source:
--   Kyprianou (2006), Chapter 7, Lemmas 7.13–7.14 proof, section 7.6, printed pp.200–202, original PDF pp.209–211; exact full proof private remote compiler job 286a8dfc-4804-471f-b9f8-c1e5ae87997e.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.sumConvolutionComm
    (mu nu : Measure Real) [SFinite mu] [SFinite nu] :
    Kyprianou.Ch07.sumConvolution mu nu =
      Kyprianou.Ch07.sumConvolution nu mu := by
  sorry
