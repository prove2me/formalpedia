-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_profile_tail_decorrelation
-- name    : OAI.DirectionalTransience.actual_profile_tail_decorrelation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:03.178241+00:00
-- url     : https://prove2.me/theorems/d57e306e-d10c-4b7d-a4b7-77c4a6a3e1fd
-- title:
--   OAI.DirectionalTransience.actual_profile_tail_decorrelation: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_profile_tail_decorrelation` of [lean/OAI/Probability/Ballisticity/Estimates/DensityTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/DensityTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem actual_profile_tail_decorrelation {d : ℕ}
--       (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
--       (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ A : ℝ, 0 < A ∧
--         (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
--           dot (realPosition x.1) (realPosition (step e)) =
--             dot (realPosition x.2) (realPosition (step e)) →
--           ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
--             -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
--               2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω) ∧
--         ∃ M : ℝ, 0 ≤ M ∧
--         ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
--           (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w],
--           (∀ z x, 0 < (w z).real {x}) →
--           ∀ (g : D × Environment d → ℝ),
--             Measurable g → (∀ z, 0 ≤ g z) → Integrable g (δ.prod (environmentLaw ν)) →
--             (∫ z, g z ∂δ.prod (environmentLaw ν)) = 1 →
--             Integrable (fun z => TailDecorrelation.entropyPlus (g z)) (δ.prod (environmentLaw ν)) →
--             ∃ (j : ℕ → D → ℤ) (hj : ∀ r, Measurable (j r)),
--               (∀ z (r : ℕ) (k : ℤ),
--                 TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
--                   (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) k ≤
--                 TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
--                   (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) (j r z)) ∧
--               let Z : ZeroHeightPair e → Environment d → ℝ :=
--                 fun p => outwardCanonicalExcess e (f,true) A p.1
--               let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
--               (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
--                 Integrable (fun p => Z p z.2) (κ r z.1)) ∧
--               (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1))
--                 (δ.prod (environmentLaw ν))) ∧
--               (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
--                 (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤ M + ε) ∧
--               Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
--                 ∂δ.prod (environmentLaw ν)) atTop ≤ M
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.PairAtHeight` and `OAI.TailDecorrelation.entropyPlus` (definitions bundle `OAIQ242Bal000` of this split); `OAI.TailCuts.lower`, `OAI.TailCuts.score` and `OAI.TailCuts.upper` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.HorizontalLayer` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.ZeroHeightPair`, `OAI.DirectionalTransience.outwardCanonicalExcess` and `OAI.DirectionalTransience.outwardKernelMass` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.profilePairKernel` (definitions bundle `OAIQ242Bal007` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.dot`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.crossing_failure_rapidDecay` and `OAI.DirectionalTransience.stripTime_rapidDecay` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/DensityTransfer.lean (declaration OAI.DirectionalTransience.actual_profile_tail_decorrelation)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

theorem actual_profile_tail_decorrelation {d : ℕ}
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (hue : UniformElliptic ν)
    (e : Direction d) (f : Fin d) (hef : e.1 ≠ f)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᵐ ω ∂environmentLaw ν, ∀ x : Lattice d × Lattice d,
        dot (realPosition x.1) (realPosition (step e)) =
          dot (realPosition x.2) (realPosition (step e)) →
        ∀ t : ℕ, 0 < outwardKernelMass e (f,true) (t+1) x ω ∧
          -Real.log (outwardKernelMass e (f,true) (t+1) x ω) ≤
            2*A*Real.log ((t:ℝ)+2)+outwardCanonicalExcess e (f,true) A x ω) ∧
      ∃ M : ℝ, 0 ≤ M ∧
      ∀ (D : Type) [MeasurableSpace D] (δ : Measure D) [IsProbabilityMeasure δ]
        (w : Kernel D (HorizontalLayer e)) [IsFiniteKernel w],
        (∀ z x, 0 < (w z).real {x}) →
        ∀ (g : D × Environment d → ℝ),
          Measurable g → (∀ z, 0 ≤ g z) → Integrable g (δ.prod (environmentLaw ν)) →
          (∫ z, g z ∂δ.prod (environmentLaw ν)) = 1 →
          Integrable (fun z => TailDecorrelation.entropyPlus (g z)) (δ.prod (environmentLaw ν)) →
          ∃ (j : ℕ → D → ℤ) (hj : ∀ r, Measurable (j r)),
            (∀ z (r : ℕ) (k : ℤ),
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) k ≤
              TailCuts.score (TailCuts.lower ((w z).map (fun x => x.1 f)))
                (TailCuts.upper ((w z).map (fun x => x.1 f))) (r:ℤ) (j r z)) ∧
            let Z : ZeroHeightPair e → Environment d → ℝ :=
              fun p => outwardCanonicalExcess e (f,true) A p.1
            let κ := fun r : ℕ => profilePairKernel e f w (r:ℤ) (j r) (hj r)
            (∀ r, ∀ᵐ z ∂δ.prod (environmentLaw ν), g z ≠ 0 →
              Integrable (fun p => Z p z.2) (κ r z.1)) ∧
            (∀ r, Integrable (fun z => g z * (∫ p, Z p z.2 ∂κ r z.1))
              (δ.prod (environmentLaw ν))) ∧
            (∀ ε : ℝ, 0 < ε → ∀ᶠ r in atTop,
              (∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1) ∂δ.prod (environmentLaw ν)) ≤ M + ε) ∧
            Filter.limsup (fun r => ∫ z, g z * (∫ p, Z p z.2 ∂κ r z.1)
              ∂δ.prod (environmentLaw ν)) atTop ≤ M := by
  sorry

end DirectionalTransience

end

end OAI
end
