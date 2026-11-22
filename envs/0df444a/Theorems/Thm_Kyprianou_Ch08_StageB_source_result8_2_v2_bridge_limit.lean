-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_limit
-- name    : Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_limit
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T18:22:09.821929+00:00
-- url     : https://prove2.me/theorems/6fa92b45-9807-41dc-aa37-69614f7e319e
-- title:
--   Bridge 8.2 helper: slice sandwich plus factorization implies excursion exponential
-- statement:
--   Assuming the lower and upper thin-slice bounds for up-before-down expectations, scale factorization telescopes them over uniform partitions into Riemann-sum bounds whose antitone Darboux squeeze yields the excursion exponential formula. This discharges frontier group E03 (L103) of parent candidate 45943 on bridge efd9aabc. Proof route: scale existence plus upper-exit ratio gives u(x,a)=u(x,m)u(m,a) and positivity; tails finite/antitone/integrable from the height law; product bounds become exp(-Riemann sums); mesh*(tail gap)→0 squeeze to the integral. The parent bridge applies this to the two proved slice children.
-- source:
--   Isolates the limit/assembly obligation of bridge efd9aabc after 45943 confirmed the clean frontier. Takes slice bounds as hypotheses to avoid duplication; minimum decomposition with identical parent context.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_limit
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ)
    (hLaw : HasActualQExcursionHeightLaw P D ψ q n)
    (hLow : ∀ l d : ℝ, 0 < l → 0 < d →
      Real.exp (-(d * (Phi ψ q + (n (Set.Ici l)).toReal))) ≤
        upBeforeDownExpectation P D.X q l (l + d))
    (hUp : ∀ l d : ℝ, 0 < l → 0 < d →
      upBeforeDownExpectation P D.X q l (l + d) ≤
        Real.exp (-(d * (Phi ψ q + (n (Set.Ici (l + d + d))).toReal)))) :
    ∀ x a : ℝ, 0 < x → x < a →
      upBeforeDownExpectation P D.X q x a =
        Real.exp (-(∫ t in x..a, Phi ψ q + (n (Set.Ici t)).toReal)) := by
  sorry
