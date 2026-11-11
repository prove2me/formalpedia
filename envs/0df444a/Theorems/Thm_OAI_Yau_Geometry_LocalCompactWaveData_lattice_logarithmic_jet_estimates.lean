-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_LocalCompactWaveData_lattice_logarithmic_jet_estimates
-- name    : OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:09.850304+00:00
-- url     : https://prove2.me/theorems/1bb7b8fe-f6f0-4de1-a461-255ed0fd9ee4
-- title:
--   OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates` of [lean/OAI/Geometry/NodalSets/Waves/LatticeLogJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticeLogJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry.LocalCompactWaveData`, with `open Yau.Jets Set Filter`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem lattice_logarithmic_jet_estimates (hUD : U ⊆ D) (L : ℝ) (hL : 0 < L) :
--       ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
--         ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3) (x : _root_.OAI.Yau.Jets.Coord),
--         ‖x-scaledLatticePoint n z‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
--         let t := (latticeFrame a.cover hUD n z,j)
--         let V := latticeWave a.cover a.beams hUD n z j
--         ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
--         (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧ V x ≠ 0 ∧
--         (c ≤ ‖V x‖*Real.exp (-(n:ℝ)*S x) ∧ ‖V x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
--         ∀ v,
--         |(normalizedLogJet n V x v).re -
--           (fderiv ℝ S x v-a.latticeEta hUD n z j*g (scaledLatticePoint n z) (x-scaledLatticePoint n z) v)| ≤ Cr/n*‖v‖ ∧
--         |(normalizedLogJet n V x v).im - g (scaledLatticePoint n z) (a.cover.triple.q t.1 t.2) v| ≤
--           Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.coverSourceCenter`, `OAI.Yau.Geometry.latticeFrame`, `OAI.Yau.Geometry.latticeWave`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Geometry.scaledLatticePoint`, `OAI.Yau.Geometry.sourceHessian`, `OAI.Yau.Jets.Coord`, `OAI.Yau.Geometry.AdmissibleFrameTriple`, `OAI.Yau.Geometry.CompactFrameCover.Parameter`, `OAI.Yau.Geometry.CompactFrameCover.center`, `OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter`, `OAI.Yau.Geometry.CompactFrameCover.triple`, `OAI.Yau.Geometry.LocalCompactWaveData.latticeEta` and `OAI.Yau.Geometry.TripleSourceWaveData.amplitude` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Geometry.normalizedLogJet` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proofs of `OAI.Yau.Geometry.LocalCompactWaveData.actual_lattice_gaussian_small_ball`, `OAI.Yau.Geometry.LocalCompactWaveData.lattice_sign_coefficient_upper`, `OAI.Yau.Geometry.lattice_actual_derivative_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_actual_two_point_energy_fixed_domain`, `OAI.Yau.Geometry.lattice_physical_sign_subballs_fixed_domain` and `OAI.Yau.Geometry.lattice_sign_margin_probability_fixed_domain` of this split import it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Waves/LatticeLogJets.lean (declaration OAI.Yau.Geometry.LocalCompactWaveData.lattice_logarithmic_jet_estimates)

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
import Mathlib.Geometry.Manifold.PartitionOfUnity
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

theorem lattice_logarithmic_jet_estimates (hUD : U ⊆ D) (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∃ c > 0, ∃ C > 0,
      ∀ᶠ n : ℕ in atTop, ∀ (z : SourceGrid U n) (j : Fin 3) (x : _root_.OAI.Yau.Jets.Coord),
      ‖x-scaledLatticePoint n z‖ ≤ L*(n:ℝ)^(-1/2:ℝ) →
      let t := (latticeFrame a.cover hUD n z,j)
      let V := latticeWave a.cover a.beams hUD n z j
      ‖a.beams.amplitude n t x-1‖ ≤ Ca*(n:ℝ)^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖a.beams.amplitude n t x‖ ∧ ‖a.beams.amplitude n t x‖ ≤ 3/2 ∧ V x ≠ 0 ∧
      (c ≤ ‖V x‖*Real.exp (-(n:ℝ)*S x) ∧ ‖V x‖*Real.exp (-(n:ℝ)*S x) ≤ C) ∧
      ∀ v,
      |(normalizedLogJet n V x v).re -
        (fderiv ℝ S x v-a.latticeEta hUD n z j*g (scaledLatticePoint n z) (x-scaledLatticePoint n z) v)| ≤ Cr/n*‖v‖ ∧
      |(normalizedLogJet n V x v).im - g (scaledLatticePoint n z) (a.cover.triple.q t.1 t.2) v| ≤
        Ci*(n:ℝ)^(-1/2:ℝ)*‖v‖ := by
  sorry

end LocalCompactWaveData
end
end Yau.Geometry

end OAI
end
