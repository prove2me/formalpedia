-- Prove2me | Theorems.Thm_OAI_Percolation_LocalEndpointRule_quantitative_amplification_step
-- name    : OAI.Percolation.LocalEndpointRule.quantitative_amplification_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:48:43.215102+00:00
-- url     : https://prove2.me/theorems/6a146492-9a33-4421-b261-723484ad9d98
-- title:
--   OAI.Percolation.LocalEndpointRule.quantitative_amplification_step: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.LocalEndpointRule.quantitative_amplification_step` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/Connections.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/Connections.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation.LocalEndpointRule`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem quantitative_amplification_step [Nonempty E] (hconn : Connected G)
--       {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
--       (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
--       (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
--       (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
--       (i₀ : ι) (hw₀ : 0 < weight i₀)
--       (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
--       (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
--       (hu : 0 < q.successProbability p (root i₀))
--       (a t π L' : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 < π)
--       (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
--       (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
--       (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k)
--       (hbad : 16*amplificationMomentFactor k M d c a t *
--         (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ a*π)
--       (A : Hilbert V →L[ℂ] Hilbert V)
--       (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
--       ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
--         a*π/(8*amplificationMomentFactor k M d c a t) ≤ q'.successProbability p (root i₀) ∧
--         ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
--           ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.CappedBadGoodness`, `OAI.Percolation.Connected`, `OAI.Percolation.LocalEndpointRule`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.RootTransport`, `OAI.Percolation.amplificationMomentFactor`, `OAI.Percolation.binOrbitRow`, `OAI.Percolation.clusterWindowProbability`, `OAI.Percolation.inverseCodeMass`, `OAI.Percolation.matrixCoeff`, `OAI.Percolation.vertexOrbit`, `OAI.Percolation.LocalEndpointRule.normalizedKernel` and `OAI.Percolation.LocalEndpointRule.successProbability` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.degree` and `OAI.Percolation.vertexAut` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Hilbert` and `OAI.Percolation.law` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.efficient_endpoint_profiles_of_divergent_moment` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Kernel/Connections.lean (declaration OAI.Percolation.LocalEndpointRule.quantitative_amplification_step)

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
open MeasureTheory
section QuantitativeAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

theorem quantitative_amplification_step [Nonempty E] (hconn : Connected G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (k n d : ℕ) (hn : 0 < n) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a t π L' : ℝ) (ha : 0 < a) (ht : 0 ≤ t) (hπ : 0 < π)
    (hbin : a*n*π ≤ binOrbitRow G p (root i₀) n)
    (hwindow : clusterWindowProbability G p (root i₀) (n-k*M) (2*n) ≤ t*π)
    (hcode : inverseCodeMass M L^k ≤ n*q.successProbability p (root i₀)^k)
    (hbad : 16*amplificationMomentFactor k M d c a t *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (2*n+k*M) L'} ≤ a*π)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) (2*n+k*M) L',
      a*π/(8*amplificationMomentFactor k M d c a t) ≤ q'.successProbability p (root i₀) ∧
      ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧ ‖A'‖ ≤ 2*‖A‖^k ∧
        ∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ) := by
  sorry

end LocalEndpointRule
end QuantitativeAmplificationStep
end Percolation

end OAI
end
