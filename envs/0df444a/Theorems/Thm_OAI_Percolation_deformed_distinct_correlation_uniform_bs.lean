-- Prove2me | Theorems.Thm_OAI_Percolation_deformed_distinct_correlation_uniform_bs
-- name    : OAI.Percolation.deformed_distinct_correlation_uniform_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:40:07.576965+00:00
-- url     : https://prove2.me/theorems/c4ed7970-4156-43da-af9a-1b054c77ae70
-- title:
--   OAI.Percolation.deformed_distinct_correlation_uniform_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.deformed_distinct_correlation_uniform` of [lean/OAI/Probability/UnimodularPercolation/Deformation/Derivatives.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/Derivatives.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem deformed_distinct_correlation_uniform_bs (G : BondGraph V E) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
--       (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
--       (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
--       (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
--       (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
--       deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
--         (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 * (matrixCoeff (T^3) x y).re ≤
--         ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
--           deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.internalEdges` and `OAI.Percolation.neighbors` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.matrixCoeff` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.deformedClusterMass`, `OAI.Percolation.deformedSusceptibility` and `OAI.Percolation.maxSusceptibility` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Conn`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.raw_derivative_template_row_lower_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/Derivatives.lean (declaration OAI.Percolation.deformed_distinct_correlation_uniform)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
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
section UniformWeightedCorrelation
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem deformed_distinct_correlation_uniform_bs (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V) :
    deformedSusceptibility G P p k t D x * deformedSusceptibility G P p k t D y -
      (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 * (matrixCoeff (T^3) x y).re ≤
      ∫ ω, (if ¬Conn G (ω ∩ internalEdges G D) x y then
        deformedClusterMass G P p k t D ω x * deformedClusterMass G P p k t D ω y else 0) ∂law p := by
  sorry

end UniformWeightedCorrelation
end Percolation

end OAI
end
