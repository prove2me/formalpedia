-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_finiteTensorState_form_approximation
-- name    : OAI.ContinuumCoulomb.finiteTensorState_form_approximation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:02:40.268116+00:00
-- url     : https://prove2.me/theorems/96ccdc3b-4452-4566-a91d-4ec79e3192ae
-- title:
--   OAI.ContinuumCoulomb.finiteTensorState_form_approximation: intermediate lemma from OpenAI, QMA-hardness of continuum Coulomb energy (result family 275)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContinuumCoulomb.binary_coulomb_qmaHard` and `OAI.ContinuumCoulomb.unit_coulomb_qmaHard`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *QMA-hardness of continuum Coulomb energy (result family 275)*, OpenAI Math Release, September 24, 2026, result family 275, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContinuumCoulomb.finiteTensorState_form_approximation` of [lean/OAI/MathematicalPhysics/ContinuumCoulomb/ManyBody/FiniteTensorFormError.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/ManyBody/FiniteTensorFormError.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContinuumCoulomb`, with `open MeasureTheory`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem finiteTensorState_form_approximation :
--       let p := finiteTensorState (n := n+2) v hv₁ hL2 hpartial c
--       |scale*(nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
--         t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p)-
--         (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
--           ((HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
--             (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re| ≤
--         ((Q+1:ℝ)^2*ε+(1/2:ℝ)*(Q+1:ℝ)^4*η)*Coulomb.mass p
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContinuumCoulomb.PublishedSobolevSmoothDensity`, `OAI.Laughlin.State`, `OAI.ContinuumCoulomb.HubbardGlobal.oneBodyOperator`, `OAI.ContinuumCoulomb.HubbardGlobal.twoBodyOperator`, `OAI.Laughlin.Fock.Orbital` and `OAI.Laughlin.Fock.Space` (definitions bundle `OAIQ092A001` of this split); `OAI.ContinuumCoulomb.flatCoulombTensor`, `OAI.ContinuumCoulomb.flatNuclearMatrix`, `OAI.ContinuumCoulomb.flatPairCoulomb`, `OAI.ContinuumCoulomb.flatResidualMatrix`, `OAI.ContinuumCoulomb.nuclearFormIntegrable`, `OAI.ContinuumCoulomb.positionComplexLaplacian`, `OAI.Coulomb.flatSpinOrbital` and `OAI.Coulomb.spinSpaceMeasure` (definitions bundle `OAIQ092A003` of this split); `OAI.ContinuumCoulomb.finiteTensorState`, `OAI.ContinuumCoulomb.nuclearPerturbedForm`, `OAI.Laughlin.Antisymmetric`, `OAI.Laughlin.Fock.normalizedTensorExterior` and `OAI.Laughlin.Fock.occupationInner` (definitions bundle `OAIQ092A007` of this split); `OAI.ContinuumCoulomb.Configuration`, `OAI.ContinuumCoulomb.Position`, `OAI.Coulomb.H1Vector`, `OAI.Coulomb.mass`, `OAI.Coulomb.pairEnergy` and `OAI.Coulomb.position` (the published bundle `Def_ContinuumCoulombHardness`).
--
--   **Used by.** The proofs of `OAI_ContinuumCoulomb_localizedTensor_hubbard_form_error`, `OAI.ContinuumCoulomb.localizedTensor_hubbard_lower` and `OAI.ContinuumCoulomb.localized_hubbard_near_trial` of this split import it.
-- source:
--   OpenAI, QMA-hardness of continuum Coulomb energy (result family 275), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 275; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/MathematicalPhysics/ContinuumCoulomb/ManyBody/FiniteTensorFormError.lean (declaration OAI.ContinuumCoulomb.finiteTensorState_form_approximation)

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.Int.Units
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
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.MeasureTheory.Measure.Haar.Basic
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
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OAIQ092A007

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

section FormApproximation

variable (hdensity : PublishedSobolevSmoothDensity)

variable {n Q : ℕ}

variable (v r : Fin (Q+1) → Position → Fin 2 → ℂ)

variable (hv₁ : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))

variable (hv : ∀ a s, ContDiff ℝ 2 (fun x => v a x s))

variable (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)

variable (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)

variable (hr : ∀ a s, MemLp (fun x => r a x s) 2)

variable (ho : ∀ a b, (∑ s : Fin 2, ∫ x, star (v a x s)*v b x s) = if a=b then (1:ℂ) else 0)

variable (V : Position → ℝ)

variable (hV : Continuous V)

variable (E B t : ℝ)

variable (hB : ∀ x : Configuration (n+2), |∑ i, V (Coulomb.position x i)| ≤ B)

variable (heq : ∀ a s x, r a x s = (-1/2:ℂ)*positionComplexLaplacian (fun y => v a y s) x+
      (V x:ℂ)*v a x s-(E:ℂ)*v a x s)

variable (F : Position → ℝ)

variable (hN : ∀ a b, Integrable (fun z => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (v a) z)*Coulomb.flatSpinOrbital (v b) z))
      Coulomb.spinSpaceMeasure)

variable (hW : ∀ a b c d, Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (v a) z.1)*Coulomb.flatSpinOrbital (v c) z.1)*
        (star (Coulomb.flatSpinOrbital (v b) z.2)*Coulomb.flatSpinOrbital (v d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure))

variable (c : Laughlin.State (n+2) Q)

variable (hc : Laughlin.Antisymmetric c)

variable (hI : nuclearFormIntegrable F (finiteTensorState (n := n+2) v hv₁ hL2 hpartial c))

variable (scale ε η : ℝ)

variable (K : Fin (Q+1) → Fin (Q+1) → ℂ)

variable (W : Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → Fin (Q+1) → ℂ)

variable (hK : ∀ a b, ‖(scale:ℂ)*(flatResidualMatrix v r a b+flatNuclearMatrix v F a b)-K a b‖ ≤ ε)

variable (hWerror : ∀ a b c d, ‖(scale*t:ℂ)*flatCoulombTensor v a b c d-W a b c d‖ ≤ η)

include hdensity hv hr ho hV hB heq hN hW hc hI hK hWerror

theorem finiteTensorState_form_approximation :
    let p := finiteTensorState (n := n+2) v hv₁ hL2 hpartial c
    |scale*(nuclearPerturbedForm (fun x => ∑ i, V (Coulomb.position x i)) F p+
      t*Coulomb.pairEnergy p-(n+2:ℝ)*E*Coulomb.mass p)-
      (Laughlin.Fock.occupationInner Q (Laughlin.Fock.normalizedTensorExterior (n+2) Q c)
        ((HubbardGlobal.oneBodyOperator K+HubbardGlobal.twoBodyOperator W)
          (Laughlin.Fock.normalizedTensorExterior (n+2) Q c))).re| ≤
      ((Q+1:ℝ)^2*ε+(1/2:ℝ)*(Q+1:ℝ)^4*η)*Coulomb.mass p := by
  sorry

end FormApproximation

end ContinuumCoulomb

end

end OAI
end
