-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_SourceUnitCoulomb_promise_of_hubbard_interval
-- name    : OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:51:58.699555+00:00
-- url     : https://prove2.me/theorems/325d8031-935d-4e51-8336-e70efad42d1f
-- title:
--   OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceHubbardPromise.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceHubbardPromise.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb.SourceUnitCoulomb`, with `open HubbardGlobal MediatorIteration`):
--
--   ```lean
--   theorem promise_of_hubbard_interval (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
--       (s pc h k A B q ap p g : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
--       (hp : d.PolynomialPromise s) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
--       (hu : Function.Injective u)
--       (hsites : SourceNuclearProgram.sites rho C eps c s pc h k A B d = List.ofFn u)
--       (graph : Bonds (m+1) r)
--       (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
--       (hbonds : graph.toList = (SourcePositiveProgram.output s d).bonds) (t : Fin r → ℝ)
--       (ho : (value rho C U F K eps c s pc h k A B q ap d).Valid)
--       (hscale : 1 ≤ (SourceNuclearProgram.amplification rho k d:ℝ))
--       (hpowers : 60*B+s+14 ≤ p) (hgpowers : s+14 ≤ g) (hqpowers : 60*B+s+14 ≤ q)
--       (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
--           (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
--             (fun i => PlanarForcingProgram.position (u i))) graph.left graph.right t -
--         graphSourceBottom m graph.left graph.right (fun e =>
--           (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2*(graph.weight e:ℝ))| ≤
--         ((SourceContactProgram.size d:ℝ)^g)⁻¹*
--           (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
--       (hground :
--         ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t -
--           (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤
--           unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ∧
--         unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ≤
--           ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t +
--             (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal)) :
--       (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
--         value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.yes) ∧
--       ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
--         value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.no)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.CoulombPairSum.Point` and `OAI.ContinuumCoulomb.GaussianFrequency.frequency` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.BinaryHeisenberg`, `OAI.ContinuumCoulomb.realSourceGroundEnergy`, `OAI.ContinuumCoulomb.BinaryHeisenberg.PolynomialPromise`, `OAI.ContinuumCoulomb.BinaryHeisenberg.Valid`, `OAI.ContinuumCoulomb.BinaryHeisenberg.toSource`, `OAI.ContinuumCoulomb.HubbardGlobal.graphSourceBottom`, `OAI.ContinuumCoulomb.HubbardGlobal.hubbardFermionBottom`, `OAI.ContinuumCoulomb.MediatorIteration.Bond`, `OAI.ContinuumCoulomb.MediatorIteration.Bonds`, `OAI.ContinuumCoulomb.SourceContactProgram.size`, `OAI.ContinuumCoulomb.MediatorIteration.Bonds.toList` and `OAI.ContinuumCoulomb.SourcePositiveProgram.Registers` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.localizedCoulombProfile` and `OAI.ContinuumCoulomb.PlanarForcingProgram.position` (definitions bundle `OAIQ092A004` of this split); `OAI.ContinuumCoulomb.SourceNuclearProgram.amplification` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.SourcePositiveProgram.output` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedOffsiteCoulomb` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.SourceNuclearProgram.sites`, `OAI.ContinuumCoulomb.SourcePhysicalThreshold.exactHubbardEnergy` and `OAI.ContinuumCoulomb.SourceUnitCoulomb.value` (definitions bundle `OAIQ092A010` of this split); `OAI.ContinuumCoulomb.UnitCoulomb`, `OAI.ContinuumCoulomb.unitCoulombPromise`, `OAI.ContinuumCoulomb.unitGroundEnergy`, `OAI.ContinuumCoulomb.BinaryRational.value`, `OAI.ContinuumCoulomb.PromiseProblem`, `OAI.ContinuumCoulomb.UnitCoulomb.Valid` and `OAI.ContinuumCoulomb.UnitCoulomb.toData` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.exists_source_unit_reduction_with_planar_gap` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/Reduction/SourceHubbardPromise.lean (declaration OAI.ContinuumCoulomb.SourceUnitCoulomb.promise_of_hubbard_interval)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ContinuumCoulomb.SourceUnitCoulomb
open HubbardGlobal MediatorIteration

theorem promise_of_hubbard_interval (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s pc h k A B q ap p g : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C eps c s pc h k A B d = List.ofFn u)
    (graph : Bonds (m+1) r)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : graph.toList = (SourcePositiveProgram.output s d).bonds) (t : Fin r → ℝ)
    (ho : (value rho C U F K eps c s pc h k A B q ap d).Valid)
    (hscale : 1 ≤ (SourceNuclearProgram.amplification rho k d:ℝ))
    (hpowers : 60*B+s+14 ≤ p) (hgpowers : s+14 ≤ g) (hqpowers : 60*B+s+14 ≤ q)
    (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) graph.left graph.right t -
      graphSourceBottom m graph.left graph.right (fun e =>
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2*(graph.weight e:ℝ))| ≤
      ((SourceContactProgram.size d:ℝ)^g)⁻¹*
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
    (hground :
      ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t -
        (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ∧
      unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ≤
        ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t +
          (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal)) :
    (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.yes) ∧
    ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.no) := by
  sorry

end ContinuumCoulomb.SourceUnitCoulomb

end

end OAI
end
