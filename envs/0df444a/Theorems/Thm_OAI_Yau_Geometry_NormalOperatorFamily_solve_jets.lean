-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_NormalOperatorFamily_solve_jets
-- name    : OAI.Yau.Geometry.NormalOperatorFamily.solve_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:06:57.232944+00:00
-- url     : https://prove2.me/theorems/cde24ab8-56b0-488e-a184-6bfe55233a99
-- title:
--   OAI.Yau.Geometry.NormalOperatorFamily.solve_jets: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.NormalOperatorFamily.solve_jets` of [lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Filter Set MvPolynomial`, `open scoped ContDiff Topology`, `open Yau.Jets`):
--
--   ```lean
--   theorem NormalOperatorFamily.solve_jets
--       {G : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ} {b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ}
--       (hG : NormalOperatorFamily G b) (a bb s : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
--       (ha : Continuous a) (hbb : Continuous bb) (hs : Continuous s)
--       (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
--       (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0)
--       (hlen : ∀ t, bb t^2 = a t^2+4) (hH : ∀ t i j, H t i j = H t j i)
--       (m J : ℕ) (hm : 1 ≤ m) :
--       ∃ phi A, MetricWaveJetFamily G b s a bb H m J phi A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.MetricWaveJetFamily`, `OAI.Yau.Geometry.NormalOperatorFamily`, `OAI.Yau.Jets.CPoly` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.compact_actual_metric_wave_jets` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean (declaration OAI.Yau.Geometry.NormalOperatorFamily.solve_jets)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OAIQ237Ny000

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

omit [CompactSpace T] in
theorem NormalOperatorFamily.solve_jets
    {G : T → Fin 4 → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ} {b : T → Fin 4 → _root_.OAI.Yau.Jets.Coord → ℂ}
    (hG : NormalOperatorFamily G b) (a bb s : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hbb : Continuous bb) (hs : Continuous s)
    (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0)
    (hlen : ∀ t, bb t^2 = a t^2+4) (hH : ∀ t i j, H t i j = H t j i)
    (m J : ℕ) (hm : 1 ≤ m) :
    ∃ phi A, MetricWaveJetFamily G b s a bb H m J phi A := by
  sorry

end
end Yau.Geometry

end OAI
end
