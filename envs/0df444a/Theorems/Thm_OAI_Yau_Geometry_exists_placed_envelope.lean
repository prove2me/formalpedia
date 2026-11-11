-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_exists_placed_envelope
-- name    : OAI.Yau.Geometry.exists_placed_envelope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:28:54.230833+00:00
-- url     : https://prove2.me/theorems/aa236df1-4ecf-4f1e-852a-184e0742d33f
-- title:
--   OAI.Yau.Geometry.exists_placed_envelope: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.exists_placed_envelope` of [lean/OAI/Geometry/NodalSets/Elliptic/EnvelopePlacement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/EnvelopePlacement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Set Filter MeasureTheory`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem exists_placed_envelope (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S0 : _root_.OAI.Yau.Jets.Coord → ℝ)
--       {P U K : Set _root_.OAI.Yau.Jets.Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
--       (hU : IsOpen U) (hPU : closure P ⊆ U)
--       (hDP : Icc o (fun j ↦ o j+L) ⊆ P) (hK : IsCompact K) (hKP : K ⊆ P)
--       (hg : ContDiffOn ℝ ∞ g U) (hS0 : ContDiffOn ℝ ∞ S0 U)
--       (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
--       (hsym : ∀ x ∈ Icc o (fun j ↦ o j+L), ∀ u v, g x u v = g x v u)
--       (hseed : sourceDirectionalAdmissibleOn g S0 (closure P)) (T : ℝ) :
--       ∃ (S : _root_.OAI.Yau.Jets.Coord → ℝ) (c : ℝ) (C V : Set _root_.OAI.Yau.Jets.Coord), 0 < c ∧
--         ContDiffOn ℝ ∞ S U ∧ IsCompact C ∧ C ⊆ P ∧
--         Icc o (fun j ↦ o j+L) ∪ K ⊆ C ∧
--         (∀ x ∈ Icc o (fun j ↦ o j+L) ∪ K, S0 x+c ≤ S x) ∧
--         (∀ x ∉ C, S x ≤ S0 x-c) ∧
--         IsOpen V ∧ closure P ⊆ V ∧ V ⊆ U ∧ sourceDirectionalAdmissibleOn g S V ∧
--         T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.corrugationOldSlope` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Geometry.sourceDirectionalAdmissibleOn` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_noncritical_placed_data` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/EnvelopePlacement.lean (declaration OAI.Yau.Geometry.exists_placed_envelope)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem exists_placed_envelope (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S0 : _root_.OAI.Yau.Jets.Coord → ℝ)
    {P U K : Set _root_.OAI.Yau.Jets.Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
    (hU : IsOpen U) (hPU : closure P ⊆ U)
    (hDP : Icc o (fun j ↦ o j+L) ⊆ P) (hK : IsCompact K) (hKP : K ⊆ P)
    (hg : ContDiffOn ℝ ∞ g U) (hS0 : ContDiffOn ℝ ∞ S0 U)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ Icc o (fun j ↦ o j+L), ∀ u v, g x u v = g x v u)
    (hseed : sourceDirectionalAdmissibleOn g S0 (closure P)) (T : ℝ) :
    ∃ (S : _root_.OAI.Yau.Jets.Coord → ℝ) (c : ℝ) (C V : Set _root_.OAI.Yau.Jets.Coord), 0 < c ∧
      ContDiffOn ℝ ∞ S U ∧ IsCompact C ∧ C ⊆ P ∧
      Icc o (fun j ↦ o j+L) ∪ K ⊆ C ∧
      (∀ x ∈ Icc o (fun j ↦ o j+L) ∪ K, S0 x+c ≤ S x) ∧
      (∀ x ∉ C, S x ≤ S0 x-c) ∧
      IsOpen V ∧ closure P ⊆ V ∧ V ⊆ U ∧ sourceDirectionalAdmissibleOn g S V ∧
      T < ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x := by
  sorry

end
end Yau.Geometry

end OAI
end
