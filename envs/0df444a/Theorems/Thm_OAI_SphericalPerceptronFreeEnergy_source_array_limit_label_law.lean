-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_array_limit_label_law
-- name    : OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:14:32.682118+00:00
-- url     : https://prove2.me/theorems/727f0ad7-8189-4683-8195-2532f6eaf6e5
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law` of [lean/OAI/Probability/Perceptron/Variational/SynchronizedLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/SynchronizedLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem source_array_limit_label_law (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
--       (w : Fin (k+1)→ℝ) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
--       (h : ℕ→Fin (k+1)→ℝ) (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
--       (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n j, u n j≠0) (t : ℕ→ℝ≥0)
--       (hcover : ∀ b : ℕ, 0<b → ∃ j, p j=0 ∧ d j=b)
--       {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
--       (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun j => p j.val)
--         (fun j => d j.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν)) :
--       (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap` and `OAI.SphericalPerceptronFreeEnergy.stepCumulative` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceGibbsArrayLaw` and `OAI.SphericalPerceptronFreeEnergy.sourceLabelLaw` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`, `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists` and `OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/SynchronizedLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_array_limit_label_law)

import Mathlib
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Matrix
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem source_array_limit_label_law (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ)
    (w : Fin (k+1)→ℝ) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
    (h : ℕ→Fin (k+1)→ℝ) (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n j, u n j≠0) (t : ℕ→ℝ≥0)
    (hcover : ∀ b : ℕ, 0<b → ∃ j, p j=0 ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k f (fun j => p j.val)
      (fun j => d j.val) (h (s n)) (u (s n)) (stepCumulative w) (t (s n))) atTop (𝓝 ν)) :
    (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 1 0).2)=sourceLabelLaw k w := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
