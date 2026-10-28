-- Prove2me | Theorems.Thm_OAI_Percolation_exists_uniform_averaged_decrease
-- name    : OAI.Percolation.exists_uniform_averaged_decrease
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:53:24.044605+00:00
-- url     : https://prove2.me/theorems/72377824-0ab9-428d-b794-7dee87668dd2
-- title:
--   OAI.Percolation.exists_uniform_averaged_decrease: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.exists_uniform_averaged_decrease` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`, `open scoped ComplexOrder`):
--
--   ```lean
--   theorem exists_uniform_averaged_decrease (G : BondGraph V E) (hG : Function.Injective G)
--       (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
--       (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
--       (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
--       (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
--       (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
--       (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hPs : IsSelfAdjoint P) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
--         ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T → ∀ (k : ℕ), 3 ≤ k →
--         ∀ (t : ℝ), 0 ≤ t →
--         Real.exp (-t*Real.exp (C*(k:ℝ))) *
--           (rawPathAverage G (walkKernel G hloc a) k root weight
--             (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
--             (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
--               (‖P‖^k * (rootTrace root weight (T^3)).re)) ≤
--           ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RootTransport`, `OAI.Percolation.matrixCoeff` and `OAI.Percolation.rootTrace` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.deformedDerivativeMass`, `OAI.Percolation.degree`, `OAI.Percolation.maxSusceptibility`, `OAI.Percolation.rawPathAverage`, `OAI.Percolation.retainedSusceptibilityProduct`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert`, `OAI.Percolation.law` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_finite_scale_obstruction` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/AveragedDecrease.lean (declaration OAI.Percolation.exists_uniform_averaged_decrease)

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
open scoped ComplexOrder
section UniformAveragedDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]
variable {ι : Type*} [Fintype ι]
attribute [local instance] spectralRealOperatorScalarTower spectralRealOperatorSMulCommClass

theorem exists_uniform_averaged_decrease (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hK : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hPs : IsSelfAdjoint P) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T → ∀ (k : ℕ), 3 ≤ k →
      ∀ (t : ℝ), 0 ≤ t →
      Real.exp (-t*Real.exp (C*(k:ℝ))) *
        (rawPathAverage G (walkKernel G hloc a) k root weight
          (retainedSusceptibilityProduct G (walkKernel G hloc a) p t) -
          (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2 *
            (‖P‖^k * (rootTrace root weight (T^3)).re)) ≤
        ∑ i, weight i * ∫ ω, deformedDerivativeMass G (walkKernel G hloc a) p k t Set.univ ω (root i) ∂law p := by
  sorry

end UniformAveragedDecrease
end Percolation

end OAI
end
