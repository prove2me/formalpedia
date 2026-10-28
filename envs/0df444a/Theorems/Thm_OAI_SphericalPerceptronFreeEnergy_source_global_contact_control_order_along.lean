-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_global_contact_control_order_along
-- name    : OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:15:27.143593+00:00
-- url     : https://prove2.me/theorems/4951bb4b-f353-4c05-a0bc-9989079f2639
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along` of [lean/OAI/Probability/Perceptron/Control/ContactControl.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Control/ContactControl.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--    theorem source_global_contact_control_order_along [IsProbabilityMeasure P]
--       (hB : IsBrownianReal brownianEval P) :
--       controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) ≤
--         controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.SourceContactParameter`, `OAI.SphericalPerceptronFreeEnergy.boundedQuantile`, `OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw`, `OAI.SphericalPerceptronFreeEnergy.stepCumulative` and `OAI.SphericalPerceptronFreeEnergy.weightedStepTrial` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.quantileTrial`, `OAI.SphericalPerceptronFreeEnergy.sourceContactCompactDomain`, `OAI.SphericalPerceptronFreeEnergy.sourceGibbsArrayLaw` and `OAI.SphericalPerceptronFreeEnergy.sourceStepContactObjective` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.BrownianPath`, `OAI.SphericalPerceptronFreeEnergy.Time`, `OAI.SphericalPerceptronFreeEnergy.brownianEval`, `OAI.SphericalPerceptronFreeEnergy.controlValue` and `OAI.SphericalPerceptronFreeEnergy.instMeasurableSpaceBrownianPath` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.main` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Control/ContactControl.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.compactPositivePairLaw_fst_isProbability _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

variable (k : ℕ) (P : Measure BrownianPath) (g : Jet3) (p d : ℕ→ℕ)
variable (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
variable (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (hq : Monotone q)
variable (δ : ℝ) (α : ℝ≥0) (H : ℝ)
variable (c : (n : ℕ)→SourceContactParameter n k)
variable (hc : ∀ n, c n∈sourceContactCompactDomain n k α H)
variable (hmin : ∀ n, IsMinOn (sourceStepContactObjective n k P g.f
  (fun i => p i.val) (fun i => d i.val) w q (fun i => (hw i).le) hw1 δ)
  (sourceContactCompactDomain n k α H) (c n))
variable (hH : 0≤H) (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
variable {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
variable (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f (fun i => p i.val) (fun i => d i.val)
  (c (s n)).2.1 (c (s n)).2.2 (stepCumulative w) (c (s n)).1) atTop (𝓝 ν))

variable (hcap : ∀ᶠ n in atTop, (c (s n)).2.1 (Fin.last k)<H)

include hc hmin hH hcover hs hlim hcap hq in
 theorem source_global_contact_control_order_along [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) :
    controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) ≤
      controlValue P g.f (weightedStepTrial w q (fun i => (hw i).le) hw1) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
