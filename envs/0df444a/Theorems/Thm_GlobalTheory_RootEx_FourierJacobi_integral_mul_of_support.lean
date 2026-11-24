-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_integral_mul_of_support
-- name    : GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:00.261547+00:00
-- url     : https://prove2.me/theorems/41def101-77fc-465b-a3d7-d83fecde9479
-- title:
--   Fourier Jacobi: integral mul of support
-- statement:
--   The Fourier Jacobi construction uses the integral mul of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralMulOfSupport.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralMulOfSupport.lean#L83-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeHeisenbergVariableSignStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotIntFJUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalFStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralMulOfSupport
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobi
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} {ψ : AddChar k Circle} {ν : Measure k}
  {P A : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
  {fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ} {b b₀ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ}
omit [DecidableEq n] [BorelSpace k] [ValuativeRel k] [IsNonarchimedeanLocalField k] [Field k]

theorem GlobalTheory.RootEx.FourierJacobi.integral_mul_of_support {U : Set (n → k)} {Ψ f : (n → k) → ℂ} {z : ℂ} (h0 : ∀ y, y ∉ U → Ψ y = 0)
    (h1 : ∀ y ∈ U, f y = z) :
    ∫ y, Ψ y * f y ∂(Measure.pi fun _ => ν) = (∫ y, Ψ y ∂(Measure.pi fun _ => ν)) * z := by sorry
