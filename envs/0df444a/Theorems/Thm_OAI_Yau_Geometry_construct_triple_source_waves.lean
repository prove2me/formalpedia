-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_construct_triple_source_waves
-- name    : OAI.Yau.Geometry.construct_triple_source_waves
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:33.929551+00:00
-- url     : https://prove2.me/theorems/f3c26cf3-3cdc-4a5f-ae43-9d67113c7645
-- title:
--   OAI.Yau.Geometry.construct_triple_source_waves: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.construct_triple_source_waves` of [lean/OAI/Geometry/NodalSets/Waves/TripleSourceWaves.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/TripleSourceWaves.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Filter Set`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem construct_triple_source_waves
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
--       (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
--       (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
--       (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
--       (d : SourceFrameTriple g S y) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
--       (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
--       (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
--       Nonempty (TripleSourceWaveData g w S y d m J K k0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.SourceFrameTriple`, `OAI.Yau.Geometry.TripleSourceWaveData`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.metricGradient` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Target.PlacedEnvelopeData.waves_in_domain` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/TripleSourceWaves.lean (declaration OAI.Yau.Geometry.construct_triple_source_waves)

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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Mathlib.LinearAlgebra.Matrix.Adjugate
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
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem construct_triple_source_waves
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (d : SourceFrameTriple g S y) {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U)
    (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    Nonempty (TripleSourceWaveData g w S y d m J K k0) := by
  sorry

end
end Yau.Geometry

end OAI
end
