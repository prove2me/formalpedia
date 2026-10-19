-- Prove2me | Theorems.Thm_OAI_KervaireMatrix_phase_scalar_le_codim
-- name    : OAI.KervaireMatrix.phase_scalar_le_codim
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:42:53.368105+00:00
-- url     : https://prove2.me/theorems/e38bf71f-a7f2-46f9-92ea-b0f4c2c3b091
-- title:
--   Phase bound by the codimension of the fixed space
-- statement:
--   Let $A$ be a group, $D$ a finite set, and $\mathrm{Ph}$ the traced fractional phase of a unitary on $\ell^2(D\times A)$, the sum over $i\in D$ of the phases at $\delta_{(i,1)}$. For a complex square matrix $M$ indexed by a finite set, $\mathrm{fix}(M)=\dim_{\mathbb C}\ker(M-1)$ is the dimension of its fixed space. Let $M,Q$ be unitary $D\times D$ matrices with $QMQ^*=M^*$. Then the scalar tensor $M\otimes1$ satisfies
--   $$
--   \mathrm{Ph}(M\otimes1)\le\frac{|D|-\mathrm{fix}(M)}2 .
--   $$
--
--   The conjugacy of $M$ with its adjoint pairs each eigenvalue $\lambda\ne1$ with $\bar\lambda$, whose fractional phases sum to $1$, while fixed vectors contribute nothing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/FixedSpaces.lean#L198-L225

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
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces

open OAI OAI.KervaireMatrix
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
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix
open KervaireFixed KervaireSpectral KervaireRegular
open scoped Classical
variable {D A : Type*} [Fintype D] [Group A]

theorem OAI.KervaireMatrix.phase_scalar_le_codim (M Q : Matrix D D ℂ)
    (hM : M ∈ unitary (Matrix D D ℂ)) (hQ : Q ∈ unitary (Matrix D D ℂ))
    (hc : Q * M * star Q = star M) :
    let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) hM)
    KervaireMatrix.phase (scalarTensor (A := A) M) ≤
      ((Fintype.card D : ℝ) - fixedDim M) / 2 := by sorry
