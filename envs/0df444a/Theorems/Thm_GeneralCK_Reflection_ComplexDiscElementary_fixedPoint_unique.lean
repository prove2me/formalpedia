-- Prove2me | Theorems.Thm_GeneralCK_Reflection_ComplexDiscElementary_fixedPoint_unique
-- name    : GeneralCK.Reflection.ComplexDiscElementary.fixedPoint_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:03:15.576707+00:00
-- url     : https://prove2.me/theorems/bc5bf84d-36b4-45c0-82e1-8991bbed72c3
-- title:
--   Uniqueness of a contracting fixed point in the contact disc
-- statement:
--   Let $D=\{z\in\mathbb C:|z|\le4/5\}$ and let $f:\mathbb C\to\mathbb C$ be $49/50$-Lipschitz on $D$. If $c,d\in D$ satisfy $f(c)=c$ and $f(d)=d$, then $$c=d.$$ The conclusion is uniqueness conditional on the stated fixed-point equations; it does not assert existence.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexDiscElementary.lean#L102-L117

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
open Set

theorem GeneralCK.Reflection.ComplexDiscElementary.fixedPoint_unique
    {f : ℂ → ℂ} {c d : ℂ}
    (hf : LipschitzOnWith (49 / 50 : NNReal) f
      (Metric.closedBall 0 (4 / 5 : ℝ)))
    (hc : c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hd : d ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hfc : f c = c) (hfd : f d = d) : c = d := by sorry
