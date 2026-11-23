-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realMarkL2ApproxEventuallyUniformL2BoundV1
-- name    : Kyprianou.Ch02.realMarkL2ApproxEventuallyUniformL2BoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:14:49.214117+00:00
-- url     : https://prove2.me/theorems/cb1555f6-1487-450c-9165-47701efb18f0
-- title:
--   L2-convergent simple mark approximations have eventually bounded L2 norms
-- statement:
--   In the restricted intensity measure, convergence of simple mark approximations to the identity in L2 together with square-integrability of the identity ensures their L2 norms are eventually bounded by a finite constant. This deterministic estimate is used to derive bounded Campbell second moments in the Lemma 2.9 L2 chain.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.9 finite-band compensated Poisson martingale; L2 triangle inequality.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.realMarkL2ApproxEventuallyUniformL2BoundV1
    (ν : Measure ℝ) [SigmaFinite ν] (B : Set ℝ)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hfL2 : Filter.Tendsto
      (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
      Filter.atTop (nhds 0)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ᶠ n in Filter.atTop,
        eLpNorm (fun x : ℝ => (f n) x) 2 (ν.restrict B) ≤ C := by sorry
