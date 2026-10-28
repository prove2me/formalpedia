-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_monomial_tendsto
-- name    : OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:16:39.149685+00:00
-- url     : https://prove2.me/theorems/3298deb0-f742-42ae-a88f-08c28dea29a4
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto` of [lean/OAI/Probability/Perceptron/Variational/CompactGGDensity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/CompactGGDensity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   lemma source_contact_monomial_tendsto (j r : ℕ) (i : Fin r)
--       (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
--       Tendsto (fun n => compactGGDefect (sourceGibbsArrayLaw n k f (fun a=>p a.val)
--         (fun a=>d a.val) (h n) (u n) z (t n)) r i G (compactJointMonomial (p j) (d j))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.CompactBlock`, `OAI.SphericalPerceptronFreeEnergy.CompactJointOverlap`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.compactGGDefect` and `OAI.SphericalPerceptronFreeEnergy.compactJointMonomial` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.quadraticBoxPenalty` and `OAI.SphericalPerceptronFreeEnergy.sourcePenaltyWeight` (definitions bundle `OAIQ61Pf001` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceExpectedPressure` and `OAI.SphericalPerceptronFreeEnergy.sourceGibbsArrayLaw` (definitions bundle `OAIQ61Pf002` of this split).
--
--   **Used by.** The proofs of `OAI.SphericalPerceptronFreeEnergy.bulk_single_limit_exists`, `OAI.SphericalPerceptronFreeEnergy.labelProfile_reference_full_exists`, `OAI.SphericalPerceptronFreeEnergy.main`, `OAI.SphericalPerceptronFreeEnergy.quantile_marked_pair_reference_exists`, `OAI.SphericalPerceptronFreeEnergy.quantile_pair_reference_exists` and `OAI.SphericalPerceptronFreeEnergy.source_global_contact_control_order_along` of this split import it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/CompactGGDensity.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto)

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
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

variable (k : ℕ) (f : ℝ →ᵇ ℝ) (p d : ℕ→ℕ) (z : Fin k→ℝ)
variable (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
variable (t : ℕ→ℝ≥0) (h : ℕ→Fin (k+1)→ℝ)
variable (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
variable (u : (n : ℕ)→Fin (n+1)→ℝ) (hu : ∀ n, u n∈Icc (fun _=>1) (fun _=>2))
variable (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
  sourceExpectedPressure n k f (fun j=>p j.val) (fun j=>d j.val) (h n) z (t n) v)
  (Icc (fun _ : Fin (n+1)=>1) (fun _=>2)) (u n))
variable {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)

include hz hz0 hz1 hh0 hh hu hmin hH hhH ht in
lemma source_contact_monomial_tendsto (j r : ℕ) (i : Fin r)
    (G : CompactBlock CompactJointOverlap r →ᵇ ℝ) :
    Tendsto (fun n => compactGGDefect (sourceGibbsArrayLaw n k f (fun a=>p a.val)
      (fun a=>d a.val) (h n) (u n) z (t n)) r i G (compactJointMonomial (p j) (d j))) atTop (𝓝 0) := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
