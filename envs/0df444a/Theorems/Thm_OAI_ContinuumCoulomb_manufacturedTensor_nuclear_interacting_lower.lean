-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_manufacturedTensor_nuclear_interacting_lower
-- name    : OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:53:34.256098+00:00
-- url     : https://prove2.me/theorems/6b24a139-98fa-452c-b35c-1cb92eefede8
-- title:
--   OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedNuclearTensorLower.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedNuclearTensorLower.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open MeasureTheory`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem manufacturedTensor_nuclear_interacting_lower
--       (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R ε : ℝ}
--       (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H)
--       (hfreq : 1 ≤ freq) (hrelation : freq^2 = 4*Real.pi*rho)
--       (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
--       (scale : ℝ) (hscale : 0 ≤ scale) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
--       (hD : 2 ≤ D) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
--       (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
--       (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
--         localizedCounterterm freq u i/scale ≤ η)
--       (hε : 0 ≤ ε)
--       (herr : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
--         manufacturedOrbitalSquaredError rho H S freq η D R u j) ≤ ε^2)
--       (F : Position → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
--       (herror : ∀ (z : Coulomb.H1Vector (n+1)) s i,
--         Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
--         (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
--           B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2))
--       (w : Coulomb.H1Vector (n+1)) (a g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
--       let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
--       let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
--         (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
--         (localizedSpinMode_partial_memLp hf u) w
--       let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
--       let V : Configuration (n+1) → ℝ := fun x => ∑ i,
--         manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
--       let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
--       let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
--         ((-1/2:ℝ)+freq/2))+ε
--       (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
--       (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤ nuclearPerturbedForm V F q →
--       (E+a-3*(ε^2+t^2*(8*(n+1:ℝ)^3*K)+B^2*((n+1:ℝ)+2*K)*(n+1))/g)*Coulomb.mass w ≤
--         nuclearPerturbedForm V F w+t*Coulomb.pairEnergy w
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PlanarPosition` (definitions bundle `OAIQ092A000` of this split); `OAI.ContinuumCoulomb.PublishedSobolevSmoothDensity` (definitions bundle `OAIQ092A001` of this split); `OAI.Coulomb.H1Vector.add` and `OAI.Coulomb.H1Vector.scale` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.finiteTensorProjection`, `OAI.ContinuumCoulomb.localizedOverlapBound`, `OAI.ContinuumCoulomb.localizedSpinMode` and `OAI.ContinuumCoulomb.nuclearPerturbedForm` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.PlanarSobolev.wellBound` (definitions bundle `OAIQ092A008` of this split); `OAI.ContinuumCoulomb.localizedCounterterm`, `OAI.ContinuumCoulomb.localizedSpinMode_C1`, `OAI.ContinuumCoulomb.localizedSpinMode_memLp` and `OAI.ContinuumCoulomb.manufacturedSlabPotential` (definitions bundle `OAIQ092A009` of this split); `OAI.ContinuumCoulomb.localizedSpinMode_partial_memLp` and `OAI.ContinuumCoulomb.manufacturedOrbitalSquaredError` (definitions bundle `OAIQ092A010` of this split); `OAI.ContinuumCoulomb.Configuration`, `OAI.ContinuumCoulomb.Position`, `OAI.Coulomb.Configuration`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.Spins`, `OAI.Coulomb.kinetic`, `OAI.Coulomb.mass`, `OAI.Coulomb.pairEnergy` and `OAI.Coulomb.position` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proof of `OAI.ContinuumCoulomb.manufactured_grid_ground_bounds` of this split imports it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/OneParticle/ManufacturedNuclearTensorLower.lean (declaration OAI.ContinuumCoulomb.manufacturedTensor_nuclear_interacting_lower)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem manufacturedTensor_nuclear_interacting_lower
    (hdensity : PublishedSobolevSmoothDensity) {rho H S freq η D R ε : ℝ}
    (hrho : 0 ≤ rho) (hH : 0 < H) (hS : 0 < S) (hSH : S^3 ≤ H)
    (hfreq : 1 ≤ freq) (hrelation : freq^2 = 4*Real.pi*rho)
    (hR : 0 < R) (hRH : R ≤ H/2) (hRS : R ≤ S)
    (scale : ℝ) (hscale : 0 ≤ scale) {m n : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hD : 2 ≤ D) (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2) (hη : 0 ≤ η)
    (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
      localizedCounterterm freq u i/scale ≤ η)
    (hε : 0 ≤ ε)
    (herr : (n+1:ℝ)^2*(8*(m+1:ℕ)^2*∑ j,
      manufacturedOrbitalSquaredError rho H S freq η D R u j) ≤ ε^2)
    (F : Position → ℝ) (hF : Measurable F) (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ (z : Coulomb.H1Vector (n+1)) s i,
      Integrable (fun x => |F (Coulomb.position x i)| * ‖z.value s x‖^2) ∧
      (∫ x, |F (Coulomb.position x i)| * ‖z.value s x‖^2) ≤
        B*((∫ x, ‖z.value s x‖^2)+∑ k : Fin 3, ∫ x, ‖z.gradient s (i,k) x‖^2))
    (w : Coulomb.H1Vector (n+1)) (a g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) :
    let hf : 0 < freq := lt_of_lt_of_le zero_lt_one hfreq
    let p : Coulomb.H1Vector (n+1) := finiteTensorProjection (localizedSpinMode freq u)
      (localizedSpinMode_C1 freq u) (localizedSpinMode_memLp hf u)
      (localizedSpinMode_partial_memLp hf u) w
    let q : Coulomb.H1Vector (n+1) := w.add (Coulomb.H1Vector.scale (-1) p)
    let V : Configuration (n+1) → ℝ := fun x => ∑ i,
      manufacturedSlabPotential rho H S freq scale u (Coulomb.position x i)
    let E : ℝ := (n+1:ℝ)*((-1/2:ℝ)+freq/2)
    let K : ℝ := (n+1:ℝ)*(((m+1:ℕ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+ε
    (E+a)*Coulomb.mass p ≤ nuclearPerturbedForm V F p+t*Coulomb.pairEnergy p →
    (E+a)*Coulomb.mass q+g*(Coulomb.mass q+2*Coulomb.kinetic q) ≤ nuclearPerturbedForm V F q →
    (E+a-3*(ε^2+t^2*(8*(n+1:ℝ)^3*K)+B^2*((n+1:ℝ)+2*K)*(n+1))/g)*Coulomb.mass w ≤
      nuclearPerturbedForm V F w+t*Coulomb.pairEnergy w := by
  sorry

end ContinuumCoulomb

end

end OAI
end
