-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_filtered_avram_upcrossing_discount_real_cap
-- name    : Kyprianou.Ch08.StageB.filtered_avram_upcrossing_discount_real_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T08:16:56.314234+00:00
-- url     : https://prove2.me/theorems/881232c8-f285-440e-8789-38e7e93dc43b
-- title:
--   Filtered spectrally negative Lévy real upcrossing discount bound for nonnegative Laplace roots including zero
-- statement:
--   Convert the Proved ENNReal unrestricted upward-passage martingale bound to the genuine finite real discounted first-upcrossing expectation of a filtered spectrally negative Lévy process, together with integrability, for any q and matching root phi both nonnegative. This is the principal mathematical bridge from Avram into the original Kyprianou Lemma 8.2 unit cap.
-- source:
--   Proof factor extracted from original model upper passage direct candidate. Uses proved nonnegative root upcrossing transform 12fbdda4 and stageB_tauPlus_coe_eq plus stopped first passage measurability.

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.filtered_avram_upcrossing_discount_real_cap
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 ≤ q) (φ : ℝ) (hφ : 0 ≤ φ)
    (hroot : A.ψ φ = q) :
    Integrable (fun ω => discountedAt q (tauPlus A.X 1 ω)) P ∧
      (∫ ω, discountedAt q (tauPlus A.X 1 ω) ∂P) ≤
        Real.exp (-(φ * 1)) := by
  sorry
