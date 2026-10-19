-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_incidence_integral_constant
-- name    : OAI.KervaireIncidenceCurrent.incidence_integral_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:35:05.021225+00:00
-- url     : https://prove2.me/theorems/003532ee-1acf-4307-861c-0b83e4d8468b
-- title:
--   Homotopy invariance of incidence currents
-- statement:
--   For finite index sets $K,R$ and a map $f:\mathbb R\times M_K\to M_{K\sqcup R}$, where $M_I$ denotes complex $I\times I$ matrices, the incidence map is
--   $$
--   \mathrm{inc}_f(t;X,P,Q)=f(t,X)\,P\,\mathrm{diag}(1,Q^*)\,P^*,
--   $$
--   defined for $X\in M_K$, $P\in M_{K\sqcup R}$ and $Q\in M_R$.
--
--   Let $f$ be smooth with $f(t,X)$ unitary for unitary $X$, and choose bases of the skew $K$-matrices and skew $R$-matrices that are orthogonal for the trace pairing, and a basis of $R\times K$ matrices. Let $b_0,\dots,b_n$ be the resulting horizontal basis. Then for every smooth $(n+1)$-form $\omega$ on $M_{K\sqcup R}$, the Haar integral over the unitary group of the algebra
--   $$
--   \int\omega_{\mathrm{inc}_f(t,p)}\bigl(d\,\mathrm{inc}_f(p\,\mathrm{dir}\,b_0),\dots,d\,\mathrm{inc}_f(p\,\mathrm{dir}\,b_n)\bigr)\,dp
--   $$
--   does not depend on $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean#L319-L345

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
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent

open OAI OAI.KervaireIncidenceCurrent
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
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open MeasureTheory
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
  {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))
  [MeasurableSpace (unitary (Alg K R))] [BorelSpace (unitary (Alg K R))]
  {μ : Measure (unitary (Alg K R))} [IsFiniteMeasure μ] [IsMulRightInvariant μ]

omit [Fintype IZ] in
theorem OAI.KervaireIncidenceCurrent.incidence_integral_constant {n : ℕ} (e : (IK ⊕ IR ⊕ IZ) ≃ Fin (n+1))
    (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (hu : ∀ t (X : unitary (Mat K)), f (t,(X : Mat K)) ∈ unitary (Mat (K ⊕ R)))
    (form : Mat (K ⊕ R) → Mat (K ⊕ R) [⋀^Fin (n+1)]→L[ℝ] ℝ)
    (hform : ContDiff ℝ ∞ form) (t₀ t₁ : ℝ) :
    let b := (horizontalBasis bK bR bZ).reindex e
    (∫ p : unitary (Alg K R), form (incidence f (t₀,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₀,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) =
    (∫ p : unitary (Alg K R), form (incidence f (t₁,(p : Alg K R)))
      (fun i ↦ fderiv ℝ (incidence f) (t₁,(p : Alg K R))
        (0,(p : Alg K R)*(direction (b i) : Alg K R))) ∂μ) := by sorry
