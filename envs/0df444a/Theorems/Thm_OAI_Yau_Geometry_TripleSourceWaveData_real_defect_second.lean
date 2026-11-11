-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_TripleSourceWaveData_real_defect_second
-- name    : OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:13.806638+00:00
-- url     : https://prove2.me/theorems/b17c3ffb-3f3e-4ca2-9f03-1a4e249731e5
-- title:
--   OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second` of [lean/OAI/Geometry/NodalSets/Elliptic/RealPhaseJet.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/RealPhaseJet.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry.TripleSourceWaveData`, with `open Yau.Jets Set Metric`, `open scoped ContDiff`):
--
--   ```lean
--   lemma real_defect_second (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
--       (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
--       (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : _root_.OAI.Yau.Jets.Coord) :
--       fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = -b.eta t*g (y t.1) u v
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.SourceFrameTriple`, `OAI.Yau.Geometry.TripleSourceWaveData`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Jets.Coord`, `OAI.Yau.Geometry.TripleSourceWaveData.eta` and `OAI.Yau.Geometry.TripleSourceWaveData.realDefect` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/RealPhaseJet.lean (declaration OAI.Yau.Geometry.TripleSourceWaveData.real_defect_second)

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
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

variable {T : Type*} [TopologicalSpace T]
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {y : T → _root_.OAI.Yau.Jets.Coord}
  {d : SourceFrameTriple g S y}
  {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

lemma real_defect_second (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) (t : T × Fin 3) (u v : _root_.OAI.Yau.Jets.Coord) :
    fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) u v = -b.eta t*g (y t.1) u v := by
  sorry

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
end
