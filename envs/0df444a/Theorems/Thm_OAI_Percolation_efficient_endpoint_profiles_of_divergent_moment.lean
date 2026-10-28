-- Prove2me | Theorems.Thm_OAI_Percolation_efficient_endpoint_profiles_of_divergent_moment
-- name    : OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:51:14.741356+00:00
-- url     : https://prove2.me/theorems/3ece5fe7-c42b-4836-8f72-88637a0d0591
-- title:
--   OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Clusters/Resampling.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Clusters/Resampling.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory Filter`):
--
--   ```lean
--   theorem efficient_endpoint_profiles_of_divergent_moment
--       [Countable V] [Countable E] [Nonempty V] [Nonempty E]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
--       (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
--       (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
--       (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
--       (hfin : ∀ i, ∀ᵐ ω ∂law p, (cluster G ω (root i)).Finite)
--       (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
--       (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
--       (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
--       ∃ i, ∀ η : ℝ, 0 < η → ∀ R : ℝ,
--         ∃ q : EndpointProfile G hloc p (root i) (1/2+ε),
--           2 ≤ q.cap ∧ 1 < q.H ∧ R < q.H ∧ q.U+q.m < η*q.H
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.EndpointProfile`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RootTransport`, `OAI.Percolation.EndpointProfile.H`, `OAI.Percolation.EndpointProfile.U` and `OAI.Percolation.EndpointProfile.m` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.hV` and `OAI.Percolation.vertexAut` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.cluster` and `OAI.Percolation.law` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proofs of `OAI_Percolation_critical_rootTriangleSqrt_derivative` and `OAI.Percolation.critical_root_power_integrable` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Clusters/Resampling.lean (declaration OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment)

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EfficientEndpointProfiles
attribute [local instance] Classical.propDecidable Classical.decEq

theorem efficient_endpoint_profiles_of_divergent_moment
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law p, (cluster G ω (root i)).Finite)
    (α β ε : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hsmall : β+(1/2+ε) < 1)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ i, ∀ η : ℝ, 0 < η → ∀ R : ℝ,
      ∃ q : EndpointProfile G hloc p (root i) (1/2+ε),
        2 ≤ q.cap ∧ 1 < q.H ∧ R < q.H ∧ q.U+q.m < η*q.H := by
  sorry

end EfficientEndpointProfiles

end Percolation

end OAI
end
