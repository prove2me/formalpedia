-- Prove2me | Theorems.Thm_OAI_Percolation_almost_linear_susceptibility
-- name    : OAI.Percolation.almost_linear_susceptibility
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:48:39.30435+00:00
-- url     : https://prove2.me/theorems/da8a4ded-0e5c-4b8b-b72e-2262d7f9e717
-- title:
--   OAI.Percolation.almost_linear_susceptibility: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.almost_linear_susceptibility` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/TailBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/TailBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory Filter`):
--
--   ```lean
--   theorem almost_linear_susceptibility
--       [Countable V] [Countable E] [Nonempty V] [Nonempty E]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
--       (hqt : QuasiTransitive G) (hh : 0 < hV G)
--       {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
--       (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
--       (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
--       (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
--       (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
--       (η : ℝ) (hη : 0 < η) :
--       ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
--         susceptibility G p x ≤ D*((pc G:ℝ)-(p:ℝ))^(-1-η)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RootTransport` and `OAI.Percolation.susceptibility` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.hV` and `OAI.Percolation.vertexAut` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.cluster`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proofs of `OAI.Percolation.critical_bounded_of_transport_finiteness` and `OAI.Percolation.critical_rootTriangle_subpower` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Exploration/TailBounds.lean (declaration OAI.Percolation.almost_linear_susceptibility)

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
section SourceAlmostLinear
attribute [local instance] Classical.propDecidable Classical.decEq

theorem almost_linear_susceptibility
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ D*((pc G:ℝ)-(p:ℝ))^(-1-η) := by
  sorry

end SourceAlmostLinear
end Percolation

end OAI
end
