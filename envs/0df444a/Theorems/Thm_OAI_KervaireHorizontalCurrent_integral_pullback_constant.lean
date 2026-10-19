-- Prove2me | Theorems.Thm_OAI_KervaireHorizontalCurrent_integral_pullback_constant
-- name    : OAI.KervaireHorizontalCurrent.integral_pullback_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:27:18.875819+00:00
-- url     : https://prove2.me/theorems/89914cec-5f74-4dfc-bfac-826702e6e9bd
-- title:
--   Pulled-back currents are invariant under homotopy
-- statement:
--   Let $B$ be a finite-dimensional real C*-algebra whose unitary group $U(B)$ is compact, with a finite right-invariant measure $\mu$ (Haar measure). Let $a_0,\dots,a_n$ be skew-adjoint, $C$ a finite-dimensional C*-algebra whose skew part has dimension at most $n+1$, and $f:\mathbb R\times B\to C$ smooth with $f(t,x)$ unitary for unitary $x$. Suppose the differential of $f$ sends each bracket direction $x[a_i,a_j]$ into the span of the directions $xa_l$ with $l\ne i,j$. Then for every smooth $(n+1)$-form $\omega$ on $C$,
--   $$
--   \int\omega_{f(t,x)}\bigl(df(0,xa_0),\dots,df(0,xa_n)\bigr)\,d\mu(x)
--   $$
--   does not depend on $t$.
--
--   This is the homotopy invariance of the degree-type currents attached to incidence maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean#L241-L313

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback

open OAI OAI.KervaireHorizontalCurrent
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
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open MeasureTheory ContinuousAlternatingMap VectorField
open KervaireUnitaryHaarCurrent KervaireUnitaryTangent
open scoped ContDiff
attribute [local instance] OAI.KervaireHorizontalCurrent.instNormedAlgebraRat_oAI
variable {B C : Type*} [CStarAlgebra B] [CStarAlgebra C]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ C]
  [CompactSpace (unitary B)] [MeasurableSpace (unitary B)] [BorelSpace (unitary B)]
  {μ : Measure (unitary B)} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

theorem OAI.KervaireHorizontalCurrent.integral_pullback_constant {n : ℕ} (a : Fin (n+1) → skewAdjoint.submodule ℝ B)
    {f : (ℝ × B) → C} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (x : unitary B), f (t,(x : B)) ∈ unitary C)
    (hdim : Module.finrank ℝ (skewAdjoint.submodule ℝ C) ≤ n+1)
    (hbr : ∀ t (x : unitary B) (i j : Fin (n+1)), i ≠ j →
      ∃ c : Fin (n+1) → ℝ, c i = 0 ∧ c j = 0 ∧
        fderiv ℝ f (t,(x : B)) (0,(x : B)*((a i : B)*(a j : B)-(a j : B)*(a i : B))) =
          ∑ l, c l • fderiv ℝ f (t,(x : B)) (0,(x : B)*(a l : B)))
    (form : C → C [⋀^Fin (n+1)]→L[ℝ] ℝ) (hform : ContDiff ℝ ∞ form) (t₀ t₁ : ℝ) :
    (∫ x : unitary B, form (f (t₀,(x : B)))
        (fun i ↦ fderiv ℝ f (t₀,(x : B)) (0,(x : B)*(a i : B))) ∂μ) =
    (∫ x : unitary B, form (f (t₁,(x : B)))
        (fun i ↦ fderiv ℝ f (t₁,(x : B)) (0,(x : B)*(a i : B))) ∂μ) := by sorry
