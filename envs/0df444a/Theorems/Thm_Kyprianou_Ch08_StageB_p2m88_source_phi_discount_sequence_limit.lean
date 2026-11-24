-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_source_phi_discount_sequence_limit
-- name    : Kyprianou.Ch08.StageB.p2m88_source_phi_discount_sequence_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:39:33.069547+00:00
-- url     : https://prove2.me/theorems/94e9616b-5fa7-4ea0-8a5b-3038012a13ae
-- title:
--   Largest nonnegative source root converges as positive discount vanishes
-- statement:
--   Transfer the source exponent to the Avram Lévy version and use its proved transform-domain bridge. The root at positive discount is at least the zero-discount root; every greater level has strictly positive exponent, so eventually bounds the positive-discount roots above.
-- source:
--   Kyprianou (2006), Corollary 8.8, q decreasing to zero.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped ENNReal NNReal

namespace Kyprianou.Ch08.StageB
 theorem p2m88_source_phi_discount_sequence_limit :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      ∀ r : ℕ → ℝ, (∀ n, 0 < r n) → Tendsto r atTop (nhds 0) →
      Tendsto (fun n => Phi ψ (r n)) atTop (nhds (Phi ψ 0)) := by
  sorry
end Kyprianou.Ch08.StageB
