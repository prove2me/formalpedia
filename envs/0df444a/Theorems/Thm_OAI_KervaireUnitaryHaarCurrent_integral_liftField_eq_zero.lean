-- Prove2me | Theorems.Thm_OAI_KervaireUnitaryHaarCurrent_integral_liftField_eq_zero
-- name    : OAI.KervaireUnitaryHaarCurrent.integral_liftField_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:25:55.851973+00:00
-- url     : https://prove2.me/theorems/0d4cda2c-fcb8-44a9-baf0-27a0299a05b1
-- title:
--   Lifted right-invariant fields are divergence-free on the time cylinder
-- statement:
--   Let $B$ be a finite-dimensional real C*-algebra whose unitary group $U(B)$ is compact, with a finite right-invariant measure $\mu$ (Haar measure). For every $t\in\mathbb R$, smooth $g:\mathbb R\times B\to\mathbb R$ and skew-adjoint $a$, the lifted field $(s,x)\mapsto(0,xa)$ satisfies
--   $$
--   \int_{U(B)}dg_{(t,x)}(0,xa)\,d\mu(x)=0 .
--   $$
--
--   This is the divergence condition needed for homotopy invariance of currents on $\mathbb R\times U(B)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean#L265-L278

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

open OAI OAI.KervaireUnitaryHaarCurrent
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
open MeasureTheory VectorField
open scoped ContDiff
variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable [CompleteSpace B] [StarRing B] [ContinuousStar B] [StarModule ℝ B]
  [CompactSpace (unitary B)] [SecondCountableTopology (unitary B)]
  [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

theorem OAI.KervaireUnitaryHaarCurrent.integral_liftField_eq_zero (t : ℝ) {g : (ℝ × B) → ℝ} (hg : ContDiff ℝ ∞ g)
    (a : skewAdjoint.submodule ℝ B) :
    (∫ x : unitary B, fderiv ℝ g (t,(x : B)) (liftField (a : B) (t,(x : B))) ∂μ) = 0 := by sorry
