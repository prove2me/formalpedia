-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvUniformLimitIntegrableOnV1
-- name    : Kyprianou.Ch04.bvUniformLimitIntegrableOnV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:39.231386+00:00
-- url     : https://prove2.me/theorems/2997331e-86e6-4e03-ac73-ce81e8ec3776
-- title:
--   Uniform limit of integrable functions on a finite-measure set
-- statement:
--   Select a sequence of approximants with uniform error below reciprocal positive integers. The almost-everywhere sequential limit is strongly measurable; a single approximant plus a constant supplies an integrable majorant.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvUniformLimitIntegrableOnV1
    {I A : Type} [MeasurableSpace A] (L : Filter I) [L.NeBot]
    (μ : Measure A) (s : Set A) (hs : MeasurableSet s) (hμ : μ s < ⊤)
    (F : I → A → ℝ) (g : A → ℝ)
    (hF : ∀ i, IntegrableOn (F i) s μ)
    (hU : TendstoUniformlyOn F g L s) :
    IntegrableOn g s μ := by
  sorry
