-- Prove2me | Theorems.Thm_OAI_Problem336_CanonicalBrownianSampler_raw_innovation_hasLaw
-- name    : OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:39:23.961995+00:00
-- url     : https://prove2.me/theorems/07a288d5-f6a3-4b28-bd7a-6e3ff93d7804
-- title:
--   OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw: intermediate lemma from OpenAI, The free uniform spanning forest is a factor of IID
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem336.fusf_is_factor_iid`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The free uniform spanning forest is a factor of IID*, OpenAI Math Release, September 25, 2026, result family 231, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw` of [lean/OAI/Probability/SpanningForest/SpanningForest/CanonicalBrownianSampler.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SpanningForest/SpanningForest/CanonicalBrownianSampler.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem336.CanonicalBrownianSampler`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal Topology`, `open CanonicalBrownianReference`):
--
--   ```lean
--   theorem raw_innovation_hasLaw (μ : ProbabilityMeasure (I → Bool))
--       (S : I → ℕ → Finset I)
--       (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
--       HasLaw (RawInnovationSampler.rawInnovation CanonicalBrownianReference.hidden CanonicalBrownianReference.noise (PosteriorDrift.drift μ S))
--         ((noiseLaw I).map ContinuousPathLaw.raw) (law μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem336.CanonicalBrownianReference.Space`, `OAI.Problem336.CanonicalBrownianReference.hidden`, `OAI.Problem336.CanonicalBrownianReference.instMeasurableSpacePath`, `OAI.Problem336.CanonicalBrownianReference.law`, `OAI.Problem336.CanonicalBrownianReference.noise`, `OAI.Problem336.CanonicalBrownianReference.noiseLaw`, `OAI.Problem336.ContinuousPathLaw.raw`, `OAI.Problem336.GlobalWiener.Path`, `OAI.Problem336.PosteriorDrift.drift` and `OAI.Problem336.RawInnovationSampler.rawInnovation` (definitions bundle `OAIS336000` of this split).
--
--   **Used by.** The proof of `OAI.Problem336.FinalFactor.worksOnGraph` of this split imports it.
-- source:
--   OpenAI, The free uniform spanning forest is a factor of IID, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 231; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SpanningForest/SpanningForest/CanonicalBrownianSampler.lean (declaration OAI.Problem336.CanonicalBrownianSampler.raw_innovation_hasLaw)

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Definitions.Def_OAIS336000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace Problem336.CanonicalBrownianSampler

open CanonicalBrownianReference

variable {I : Type*} [countableIndices : Countable I]

attribute [local instance] OAI.Problem336.CanonicalBrownianSampler.instMeasurableSpacePath
theorem raw_innovation_hasLaw (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I)
    (hS : ∀ i, Monotone (S i)) (hcover : ∀ i j, ∃ n, j ∈ S i n) :
    HasLaw (RawInnovationSampler.rawInnovation CanonicalBrownianReference.hidden CanonicalBrownianReference.noise (PosteriorDrift.drift μ S))
      ((noiseLaw I).map ContinuousPathLaw.raw) (law μ) := by
  sorry

end Problem336.CanonicalBrownianSampler

end

end OAI
end
