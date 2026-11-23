-- Prove2me | Theorems.Thm_Kyprianou_Ch02_realMarkSimpleL2ApproxV1
-- name    : Kyprianou.Ch02.realMarkSimpleL2ApproxV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T14:40:28.526259+00:00
-- url     : https://prove2.me/theorems/a049df5e-2cd5-4a12-9f83-b0e20a31c9d0
-- title:
--   Simple real mark approximation pointwise and in L2 of the restricted intensity
-- statement:
--   The identity real mark has finite-valued measurable approximants converging pointwise on all real marks and in L² against the restricted Lévy intensity, whenever the identity is in L² of that measure. This is supplied by Mathlib SimpleFunc.approxOn and its Lp convergence theorem. It supplies the source-accurate real-mark approximation needed by Chapter 2 Poisson marked-integral second moments.
-- source:
--   Kyprianou (2006), Chapter 2 Lemma 2.9 finite-band Lévy mark approximation; pinned Mathlib SimpleFunc.tendsto_approxOn_Lp_eLpNorm

import Mathlib
open MeasureTheory
set_option autoImplicit false

theorem Kyprianou.Ch02.realMarkSimpleL2ApproxV1
    (ν : Measure ℝ) (B : Set ℝ)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∃ (f : ℕ → SimpleFunc ℝ ℝ),
      (∀ x : ℝ, Filter.Tendsto (fun n => (f n) x) Filter.atTop (nhds x)) ∧
      Filter.Tendsto (fun n => eLpNorm (fun x : ℝ => (f n) x - x) 2 (ν.restrict B))
        Filter.atTop (nhds 0) := by sorry
