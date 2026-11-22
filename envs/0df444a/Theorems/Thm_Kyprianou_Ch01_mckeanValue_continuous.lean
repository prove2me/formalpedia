-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanValue_continuous
-- name    : Kyprianou.Ch01.mckeanValue_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:24:22.629988+00:00
-- url     : https://prove2.me/theorems/d6dd6c0b-bf8b-498b-9850-56ae4d62ec14
-- title:
--   Optimal McKean value is continuous at and across exercise barrier
-- statement:
--   The piecewise McKean value function is continuous on the entire real log-price line, including the exercise barrier b=log(K phi/(1+phi)). Each branch is continuous, and at y=b the exercise value K-exp(b) equals the continuation value (K-exp b)exp(-phi*(b-b)). Rewrite strict branching into weak branching, whose boundary values agree, then apply the proved Mathlib Continuous.if_le lemma. This supplies right-continuity of the discounted pathwise Brownian value process for continuous-time optional sampling.
-- source:
--   Kyprianou (2006) Chapter 1 Theorem 1.13; continuity of the value function at smooth-fit barrier.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanValue_continuous
    (K phi : ℝ) (hK : 0 < K) (hphi : 0 < phi) :
    let barrier := Real.log (K * phi / (1 + phi))
    Continuous (mckeanValue K barrier phi) := by sorry
