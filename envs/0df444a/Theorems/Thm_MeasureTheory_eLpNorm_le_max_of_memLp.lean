-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_le_max_of_memLp
-- name    : MeasureTheory.eLpNorm_le_max_of_memLp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T19:22:26.974818+00:00
-- url     : https://prove2.me/theorems/c19ec86b-4004-40a6-99a2-7847f928676c
-- title:
--   Intermediate Lq norm bounded by the maximum of two endpoint norms
-- statement:
--   For any measure space, any normed additive group, and real exponents $0<p\le q\le r<\infty$, a function belonging to both $L^p$ and $L^r$ satisfies
--   $$\|f\|_q\le\max\{\|f\|_p,\|f\|_r\}.$$
--   In particular, it belongs to $L^q$. There is no finite-measure hypothesis. For strict intermediate exponents this follows from Hölder interpolation with $1/q=\theta/p+(1-\theta)/r$ and $0<\theta<1$; the two endpoints follow by equality. This generalizes the scalar Lebesgue-space interpolation used by Hunter.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, p. 66, Theorem 3.31, interpolation display (citing Lemma 1.11); norm-valued generalization and maximum-norm corollary

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

open MeasureTheory

theorem MeasureTheory.eLpNorm_le_max_of_memLp {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {p q r : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    {f : α → E} (hfp : MemLp f (ENNReal.ofReal p) μ)
    (hfr : MemLp f (ENNReal.ofReal r) μ) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      max (eLpNorm f (ENNReal.ofReal p) μ) (eLpNorm f (ENNReal.ofReal r) μ) := by sorry
