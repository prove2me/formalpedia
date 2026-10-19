-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_frame_diagonal
-- name    : OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:31:29.472991+00:00
-- url     : https://prove2.me/theorems/444fb206-1fae-4905-8d49-1d222d827594
-- title:
--   Frame rotations act as compensated rotations of the last factor
-- statement:
--   For finite index sets $K,R$ and a map $f:\mathbb R\times M_K\to M_{K\sqcup R}$, where $M_I$ denotes complex $I\times I$ matrices, the incidence map is
--   $$
--   \mathrm{inc}_f(t;X,P,Q)=f(t,X)\,P\,\mathrm{diag}(1,Q^*)\,P^*,
--   $$
--   defined for $X\in M_K$, $P\in M_{K\sqcup R}$ and $Q\in M_R$.
--
--   Let $Q$ be a matrix, $T\in U(R)$, and $U,V$ skew-Hermitian on $K$ and $R$. At $(t;X,Q,T)$, moving the middle factor in the direction $Q\,\mathrm{diag}(U,V)$ has the same first-order effect as moving the last factor in the direction $T(T^*VT-V)$:
--   $$
--   d\,\mathrm{inc}_f(0,0,Q\,\mathrm{diag}(U,V),0)=d\,\mathrm{inc}_f\bigl(0,0,0,T(T^*VT-V)\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceTangent.lean#L113-L131

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
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

theorem OAI.KervaireIncidenceCurrent.fderiv_frame_diagonal {f : ℝ × Mat K → Mat (K ⊕ R)} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (X : Mat K) (Q : Mat (K ⊕ R)) (T : unitary (Mat R))
    (U : skewAdjoint.submodule ℝ (Mat K)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,Q*diag U V,0) =
    fderiv ℝ (incidence f) (t,X,Q,(T : Mat R)) (0,0,0,(T : Mat R)*compensated T V) := by sorry
