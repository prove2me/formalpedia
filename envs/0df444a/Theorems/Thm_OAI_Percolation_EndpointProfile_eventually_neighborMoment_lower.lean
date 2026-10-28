-- Prove2me | Theorems.Thm_OAI_Percolation_EndpointProfile_eventually_neighborMoment_lower
-- name    : OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:48:30.846345+00:00
-- url     : https://prove2.me/theorems/468f7754-c263-4152-8d47-3bbdb96ae353
-- title:
--   OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/DistinctMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/DistinctMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.EndpointProfile`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open Filter`):
--
--   ```lean
--   theorem eventually_neighborMoment_lower [Countable V] [Countable E] [Nonempty V]
--       (hconn : Connected G) (hqt : QuasiTransitive G)
--       {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
--       (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
--       (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
--       (i₀ : ι) (hw₀ : 0 < weight i₀) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
--       (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
--       (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) (hH : 1 < q.H) :
--       ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
--         b*(rootSusceptibility G root weight p)^(2-Real.log q.geometricScale/(q.H-1)) ≤
--           rootNeighborMoment G hloc root weight p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.EndpointProfile`, `OAI.Percolation.IsAut`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RootTransport`, `OAI.Percolation.rootSusceptibility`, `OAI.Percolation.vertexOrbit`, `OAI.Percolation.EndpointProfile.H` and `OAI.Percolation.EndpointProfile.geometricScale` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.rootNeighborMoment` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.critical_root_power_integrable` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/DistinctMoments.lean (declaration OAI.Percolation.EndpointProfile.eventually_neighborMoment_lower)

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
open Filter
section ProfileNeighborMoment
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p₀ : unitInterval} {o : V} {s : ℝ}

theorem eventually_neighborMoment_lower [Countable V] [Countable E] [Nonempty V]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (q : EndpointProfile G hloc p₀ (root i₀) s) (hp₀ : 0 < (p₀:ℝ)) (hH : 1 < q.H) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ p in nhds p₀, p < pc G →
      b*(rootSusceptibility G root weight p)^(2-Real.log q.geometricScale/(q.H-1)) ≤
        rootNeighborMoment G hloc root weight p := by
  sorry

end EndpointProfile
end ProfileNeighborMoment
end Percolation

end OAI
end
