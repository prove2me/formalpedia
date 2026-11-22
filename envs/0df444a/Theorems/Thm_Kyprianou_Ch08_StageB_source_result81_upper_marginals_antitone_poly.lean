-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_marginals_antitone_poly
-- name    : Kyprianou.Ch08.StageB.source_result81_upper_marginals_antitone_poly
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T19:45:36.648535+00:00
-- url     : https://prove2.me/theorems/aa6f3646-6a27-4f19-9f1c-c7bb3c5be952
-- title:
--   Antitone paths from nonpositive time marginals at arbitrary universes
-- statement:
--   The accepted Chapter 8 antitone-path lemma generalized to an arbitrary sample-space universe. If every time marginal of a spectrally negative Lévy process is almost surely nonpositive, then almost every path is antitone.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1. Source-faithful universe-polymorphic version of the accepted source_result81_levy_marginals_antitone, needed by the public scale-transfer child because the existing helper is fixed to Ω : Type.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Topology.Sequences
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_upper_marginals_antitone_poly
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (h : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A.X t ω ≤ 0) :
    ∀ᵐ ω ∂P, Antitone (fun t : ℝ≥0 => A.X t ω) := by sorry
