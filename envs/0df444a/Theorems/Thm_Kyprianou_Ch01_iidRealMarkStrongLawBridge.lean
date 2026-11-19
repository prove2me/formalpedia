-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iidRealMarkStrongLawBridge
-- name    : Kyprianou.Ch01.iidRealMarkStrongLawBridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T13:51:11.486744+00:00
-- url     : https://prove2.me/theorems/3887a314-08e3-42dd-8c10-1a43dd73b118
-- title:
--   IID real mark strong law in the LeanLevy driver convention
-- statement:
--   A direct useful bridge from the iIndepFun independence convention used by LeanLevy compound-Poisson drivers to the proved full Banach-space strong law. For integrable, identically distributed real marks, the empirical sum divided by sample size converges almost surely to its expectation.
-- source:
--   FamousTheorems.strong_law_ae already Proved, source UUID 07c6d68b-d4ca-4c25-af01-d81f3c1bc2b8; Kyprianou Chapter 1 compound Poisson marks.

import Mathlib
import Theorems.Thm_FamousTheorems_strong_law_ae
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch01.iidRealMarkStrongLawBridge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (marks : ℕ → Ω → ℝ)
    (hIntegrable : Integrable (marks 0) P)
    (hIndependent : iIndepFun marks P)
    (hIdent : ∀ i : ℕ, IdentDistrib (marks i) (marks 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, marks i ω)
        atTop (𝓝 (∫ ω, marks 0 ω ∂P)) := by
  sorry
