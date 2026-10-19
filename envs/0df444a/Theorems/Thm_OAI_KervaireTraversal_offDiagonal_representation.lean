-- Prove2me | Theorems.Thm_OAI_KervaireTraversal_offDiagonal_representation
-- name    : OAI.KervaireTraversal.offDiagonal_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:43:37.121903+00:00
-- url     : https://prove2.me/theorems/3d22f178-dbfe-4ae7-859e-7eeda38993da
-- title:
--   Self-adjoint unitary exchanges have unitary off-diagonal blocks
-- statement:
--   Let $E$ be a finite set and $N$ a complex matrix indexed by $E\sqcup E$ that is self-adjoint and unitary, and whose two diagonal blocks vanish. Then there is a unitary $P$ on $E$ with
--   $$
--   N=\begin{pmatrix}0&P^*\\P&0\end{pmatrix}.
--   $$
--
--   Such an $N$ exchanges the two copies of $E$, and is determined by the unitary $P$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Traversal.lean#L137-L161

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
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal

open OAI OAI.KervaireTraversal
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
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem OAI.KervaireTraversal.offDiagonal_representation (N : Matrix (E ⊕ E) (E ⊕ E) ℂ)
    (hNs : star N = N) (hNu : N ∈ unitary (Matrix (E ⊕ E) (E ⊕ E) ℂ))
    (h₀ : ∀ i j, N (.inl i) (.inl j) = 0)
    (h₁ : ∀ i j, N (.inr i) (.inr j) = 0) :
    ∃ P : unitary (Matrix E E ℂ), N = fromBlocks 0 (star (P : Matrix E E ℂ)) P 0 := by sorry
