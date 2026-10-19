-- Prove2me | Theorems.Thm_OAI_KervaireHaarFlow_integral_unitary_fderiv_mul_eq_zero
-- name    : OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:25:14.463137+00:00
-- url     : https://prove2.me/theorems/e4065066-da8a-475c-b6eb-3d33234a6efa
-- title:
--   Haar integrals of derivatives along right-invariant fields vanish
-- statement:
--   Let $B$ be a finite-dimensional real C*-algebra whose unitary group $U(B)$ is compact, with a finite right-invariant measure $\mu$ (Haar measure). For every smooth $g:B\to\mathbb R$ and skew-adjoint $a\in B$,
--   $$
--   \int_{U(B)}dg_x(xa)\,d\mu(x)=0 .
--   $$
--
--   Right-invariant vector fields are divergence-free for the Haar measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean#L209-L230

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents

open OAI OAI.KervaireHaarFlow
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open NormedSpace
open scoped ContDiff
attribute [local instance] OAI.KervaireHaarFlow.instNormedAlgebraRat_oAI
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]
  [StarRing B] [ContinuousStar B] [StarModule ℝ B]
variable [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

theorem OAI.KervaireHaarFlow.integral_unitary_fderiv_mul_eq_zero {g : B → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (x : B) ((x : B) * a) ∂μ) = 0 := by sorry
