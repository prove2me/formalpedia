-- Prove2me | Theorems.Thm_OAI_Percolation_exists_finite_scale_obstruction
-- name    : OAI.Percolation.exists_finite_scale_obstruction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:51:41.11129+00:00
-- url     : https://prove2.me/theorems/8a0a7416-4dd4-4231-89e3-0e0990e44525
-- title:
--   OAI.Percolation.exists_finite_scale_obstruction: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.exists_finite_scale_obstruction` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem exists_finite_scale_obstruction
--       (G : BondGraph V E) (hG : Function.Injective G)
--       (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
--       (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G))
--       (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
--       (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
--       (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
--       (d : ℕ) (hd : ∀ z, degree G z ≤ d)
--       (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
--       ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
--         ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
--         ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
--         ∀ (A : Hilbert V →L[ℂ] Hilbert V), HasKernel G p A →
--         ∀ k : ℕ, k₀ ≤ k → ∀ B : ℝ, 0 < B →
--         let R := maxSusceptibility G p/‖A‖
--         let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
--         B*‖P‖^k ≤ 1/4 →
--         B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ ‖A‖ →
--         R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*((pc G:ℝ)/2)^(2*j) →
--         M < B*((pc G:ℝ)/2)^(2*j) → False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.Connected`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.RootTransport` and `OAI.Percolation.matrixCoeff` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.degree`, `OAI.Percolation.maxSusceptibility`, `OAI.Percolation.rootTriangle`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel`, `OAI.Percolation.Hilbert` and `OAI.Percolation.pc` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.critical_bounded_of_transport_finiteness` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Deformation/FiniteScale.lean (declaration OAI.Percolation.exists_finite_scale_obstruction)

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
section FiniteScale
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Infinite V]
variable {ι : Type*} [Fintype ι]

theorem exists_finite_scale_obstruction
    (G : BondGraph V E) (hG : Function.Injective G)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (a : ℝ) (ha : 0 < a) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ J : ℕ, 0 < J ∧ ∃ C₁ : ℝ, 0 < C₁ ∧
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (A : Hilbert V →L[ℂ] Hilbert V), HasKernel G p A →
      ∀ k : ℕ, k₀ ≤ k → ∀ B : ℝ, 0 < B →
      let R := maxSusceptibility G p/‖A‖
      let j := J+⌈C₁*Real.log (((k:ℝ)+1)*R)⌉₊
      B*‖P‖^k ≤ 1/4 →
      B*(j:ℝ)*Real.exp (C*(k:ℝ)) ≤ ‖A‖ →
      R^2*rootTriangle G root weight (p:ℝ)*‖P‖^k ≤ ε*((pc G:ℝ)/2)^(2*j) →
      M < B*((pc G:ℝ)/2)^(2*j) → False := by
  sorry

end FiniteScale
end Percolation

end OAI
end
