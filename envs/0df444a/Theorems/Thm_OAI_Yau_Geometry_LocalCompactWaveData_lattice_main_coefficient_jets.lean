-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_main_coefficient_jets
-- name    : OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:30.574224+00:00
-- url     : https://prove2.me/theorems/3b9ab280-983e-43af-a09a-ffbb238c8854
-- title:
--   OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets` of [lean/OAI/Geometry/NodalSets/Waves/LatticePlaneWaveJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticePlaneWaveJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry.LocalCompactWaveData`, with `open Yau.Jets Set Filter`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem lattice_main_coefficient_jets (hUD : U ⊆ D) (R : ℝ) (hR : 0 ≤ R)
--       (d0 : ℕ) (e : ℝ) (he : 0 < e) :
--       ∀ᶠ n : ℕ in atTop, ∀ x ∈ D, ∀ s : ℝ, 1 ≤ s →
--         ∀ (sigma : ℝ) (v : _root_.OAI.Yau.Jets.Coord), ‖v‖ ≤ R → ∀ i : SourceGrid U n × Fin 3,
--         sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) → ∀ k, k ≤ d0 →
--         ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s sigma x z -
--           (latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ))*
--             planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s z) v‖ ≤
--           e*‖latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ)‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.latticeFrame`, `OAI.Yau.Geometry.latticeWave`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Geometry.planeWave`, `OAI.Yau.Geometry.scaledLatticePoint`, `OAI.Yau.Geometry.sourceEuclideanNorm`, `OAI.Yau.Geometry.sourceHessian`, `OAI.Yau.Jets.Coord`, `OAI.Yau.Geometry.AdmissibleFrameTriple`, `OAI.Yau.Geometry.CompactFrameCover.Parameter`, `OAI.Yau.Geometry.CompactFrameCover.center`, `OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter` and `OAI.Yau.Geometry.CompactFrameCover.triple` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Geometry.normalizedRescaling` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proofs of `OAI.Yau.Geometry.LocalCompactWaveData.lattice_sign_coefficient_upper`, `OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain` and `OAI.Yau.Geometry.lattice_actual_two_point_energy_fixed_domain` of this split import it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticePlaneWaveJets.lean (declaration OAI.Yau.Geometry.LocalCompactWaveData.lattice_main_coefficient_jets)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Floor.Ring
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
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Definitions.Def_OAIQ237Ny002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ}
  {w S : _root_.OAI.Yau.Jets.Coord → ℝ}
variable {D U : Set _root_.OAI.Yau.Jets.Coord}
  {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

theorem lattice_main_coefficient_jets (hUD : U ⊆ D) (R : ℝ) (hR : 0 ≤ R)
    (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ D, ∀ s : ℝ, 1 ≤ s →
      ∀ (sigma : ℝ) (v : _root_.OAI.Yau.Jets.Coord), ‖v‖ ≤ R → ∀ i : SourceGrid U n × Fin 3,
      sourceEuclideanNorm (x-scaledLatticePoint n i.1) ≤ (n:ℝ)^(-5/12:ℝ) → ∀ k, k ≤ d0 →
      ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (latticeWave a.cover a.beams hUD n i.1 i.2) S n s sigma x z -
        (latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ))*
          planeWave (g (scaledLatticePoint n i.1) (a.cover.triple.q (latticeFrame a.cover hUD n i.1) i.2)) s z) v‖ ≤
        e*‖latticeWave a.cover a.beams hUD n i.1 i.2 x/(sigma:ℂ)‖ := by
  sorry

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end
