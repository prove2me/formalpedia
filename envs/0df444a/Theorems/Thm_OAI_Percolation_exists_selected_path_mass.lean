-- Prove2me | Theorems.Thm_OAI_Percolation_exists_selected_path_mass
-- name    : OAI.Percolation.exists_selected_path_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:51:39.003703+00:00
-- url     : https://prove2.me/theorems/91fce31f-0d2e-4dc3-84ef-6c3714cf571d
-- title:
--   OAI.Percolation.exists_selected_path_mass: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.exists_selected_path_mass` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem exists_selected_path_mass [Countable V] [Countable E] [Infinite V]
--       (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G))
--       (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
--       (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
--       (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
--       (d : ℕ) (hd : ∀ z, degree G z ≤ d) (τ : ℝ) (hτ : 0 < τ) :
--       ∃ J : ℕ, ∃ C₁ : ℝ, ∃ k₀ : ℕ, ∃ b : ℝ,
--         0 < J ∧ 0 < C₁ ∧ 3 ≤ k₀ ∧ 0 < b ∧
--         ∀ p : unitInterval, (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
--         ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
--           b ≤ rawPathAverage G (walkKernel G hloc a) k root weight
--             (fun w => if w.Selected hloc p (J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊) (τ/R) then 1 else 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RawCorridor`, `OAI.Percolation.RootTransport`, `OAI.Percolation.matrixCoeff` and `OAI.Percolation.RawCorridor.Selected` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.degree`, `OAI.Percolation.rawPathAverage`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Hilbert` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_finite_scale_obstruction` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean (declaration OAI.Percolation.exists_selected_path_mass)

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
section FullPathSelection
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem exists_selected_path_mass [Countable V] [Countable E] [Infinite V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (τ : ℝ) (hτ : 0 < τ) :
    ∃ J : ℕ, ∃ C₁ : ℝ, ∃ k₀ : ℕ, ∃ b : ℝ,
      0 < J ∧ 0 < C₁ ∧ 3 ≤ k₀ ∧ 0 < b ∧
      ∀ p : unitInterval, (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ k : ℕ, k₀ ≤ k → ∀ R : ℝ, 1 ≤ R →
        b ≤ rawPathAverage G (walkKernel G hloc a) k root weight
          (fun w => if w.Selected hloc p (J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊) (τ/R) then 1 else 0) := by
  sorry

end FullPathSelection
end Percolation

end OAI
end
