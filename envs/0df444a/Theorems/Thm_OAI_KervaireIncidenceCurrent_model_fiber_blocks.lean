-- Prove2me | Theorems.Thm_OAI_KervaireIncidenceCurrent_model_fiber_blocks
-- name    : OAI.KervaireIncidenceCurrent.model_fiber_blocks
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:37:24.509036+00:00
-- url     : https://prove2.me/theorems/3b877f9b-e227-4f5d-8b1f-f6c2f7aa3bb2
-- title:
--   The fibre of the model incidence map over the identity
-- statement:
--   Let $X\in M_K$ and let $P=\begin{pmatrix}A&B\\C&D\end{pmatrix}$ be a unitary $(K\sqcup R)$-matrix and $T\in M_R$ such that
--   $$
--   \mathrm{diag}(X,-1)\,P=P\,\mathrm{diag}(1,T).
--   $$
--   Then $X=1$, $B=0$, $C=0$, $T=-1$, and $A,D$ are unitary.
--
--   So the model incidence map hits the identity exactly at block-diagonal gauge points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceDegree.lean#L94-L124

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
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree

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

theorem OAI.KervaireIncidenceCurrent.model_fiber_blocks (X A : Mat K) (B : Matrix K R ℂ) (C : Matrix R K ℂ)
    (D T : Mat R) (hQ : fromBlocks A B C D ∈ unitary (Mat (K ⊕ R)))
    (heq : diag X (-1) * fromBlocks A B C D = fromBlocks A B C D * diag 1 T) :
    X = 1 ∧ B = 0 ∧ C = 0 ∧ T = -1 ∧ A ∈ unitary (Mat K) ∧ D ∈ unitary (Mat R) := by sorry
