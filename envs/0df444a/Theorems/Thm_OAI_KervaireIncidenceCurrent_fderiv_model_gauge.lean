-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_fderiv_model_gauge
-- name    : OAI.KervaireIncidenceCurrent.fderiv_model_gauge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:36:25.328257+00:00
-- url     : https://prove2.me/theorems/b64980f8-5dee-4fd6-8ee4-d1e5defd091b
-- title:
--   The model incidence differential at gauge points
-- statement:
--   Let $\mathrm{model}(t,X)=\mathrm{diag}(X,-1)$ and let $\mathrm{inc}$ be its incidence map. For unitaries $U\in U(K)$ and $V\in U(R)$, the gauge point is $p=(1,\mathrm{diag}(U,V),-1)$. For every horizontal vector $h$,
--   $$
--   d\,\mathrm{inc}(p\,\mathrm{dir}\,h)=\Phi_{U,V}(h),
--   $$
--   where $\Phi_{U,V}$ is an explicit real-linear isomorphism onto skew-Hermitian matrices. It is built from conjugation by $U$, the degree derivative $(A,B,Z)\mapsto\begin{pmatrix}A&2Z^*\\-2Z&-B\end{pmatrix}$, and conjugation by $\mathrm{diag}(U,V)$.
--
--   In particular the model incidence map is a local diffeomorphism at every gauge point, which are its preimages of the identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean#L265-L294

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
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy

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
open scoped ContDiff
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

theorem OAI.KervaireIncidenceCurrent.fderiv_model_gauge (t : ℝ) (U : unitary (Mat K)) (V : unitary (Mat R))
    (h : Horizontal K R) :
    fderiv ℝ (incidence model) (t,(gaugePoint U V : Alg K R))
      (0,(gaugePoint U V : Alg K R)*(direction h : Alg K R)) =
      (modelHorizontalEquiv U V h : Mat (K ⊕ R)) := by sorry
