-- Prove2me | Theorems.Thm_OAI_Percolation_critical_root_power_integrable
-- name    : OAI.Percolation.critical_root_power_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:50:10.257814+00:00
-- url     : https://prove2.me/theorems/683ca7eb-a7aa-406d-9fe2-0f4900672bf8
-- title:
--   OAI.Percolation.critical_root_power_integrable: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.critical_root_power_integrable` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/FractionalMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/FractionalMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory Filter`):
--
--   ```lean
--   theorem critical_root_power_integrable
--       [Countable V] [Countable E] [Nonempty V] [Nonempty E]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
--       (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
--       (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
--       (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
--       (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
--       (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
--       ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.RootTransport` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.hV` and `OAI.Percolation.vertexAut` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.cluster`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proofs of `OAI.Percolation.almost_linear_susceptibility`, `OAI.Percolation.critical_large_contact_bound` and `OAI.Percolation.critical_rootTriangle_subpower` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/FractionalMoments.lean (declaration OAI.Percolation.critical_root_power_integrable)

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
section CriticalRootMoments
attribute [local instance] Classical.propDecidable Classical.decEq

theorem critical_root_power_integrable
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :
    ∀ i, Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law (pc G)) := by
  sorry

end CriticalRootMoments
end Percolation

end OAI
end
