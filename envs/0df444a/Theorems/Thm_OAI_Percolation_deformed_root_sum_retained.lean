-- Prove2me | Theorems.Thm_OAI_Percolation_deformed_root_sum_retained
-- name    : OAI.Percolation.deformed_root_sum_retained
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:51:20.966421+00:00
-- url     : https://prove2.me/theorems/b695f1d7-eda7-4c42-aaa5-2a5c172db8ae
-- title:
--   OAI.Percolation.deformed_root_sum_retained: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.deformed_root_sum_retained` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem deformed_root_sum_retained (G : BondGraph V E) (hG : Function.Injective G)
--       (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (a : ℝ) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
--       (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
--       (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
--       (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hA : HasKernel G p A) (k : ℕ) (t B : ℝ) (ht : 0 ≤ t)
--       (htB : t*‖A‖ ≤ B) (hB : B*‖P‖^k ≤ 1/4) :
--       ‖A‖/(2*c) ≤ averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.averagedDeformedSusceptibility` and `OAI.Percolation.matrixCoeff` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_finite_scale_obstruction` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean (declaration OAI.Percolation.deformed_root_sum_retained)

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
section AveragedRetention
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]

theorem deformed_root_sum_retained (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hcov : ∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 1 ≤ c*weight i)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hPs : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hA : HasKernel G p A) (k : ℕ) (t B : ℝ) (ht : 0 ≤ t)
    (htB : t*‖A‖ ≤ B) (hB : B*‖P‖^k ≤ 1/4) :
    ‖A‖/(2*c) ≤ averagedDeformedSusceptibility G (walkKernel G hloc a) p k root weight t := by
  sorry

end AveragedRetention
end Percolation

end OAI
end
