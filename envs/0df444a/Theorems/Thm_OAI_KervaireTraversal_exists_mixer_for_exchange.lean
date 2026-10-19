-- Prove2me | Theorems.Thm_OAI_KervaireTraversal_exists_mixer_for_exchange
-- name    : OAI.KervaireTraversal.exists_mixer_for_exchange
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:44:23.051357+00:00
-- url     : https://prove2.me/theorems/dd34bea1-e625-4fc5-9eb2-c3f58e3f90e9
-- title:
--   A scalar mixer with a large fixed space
-- statement:
--   Let $I$ be finite, $K$ finite and nonempty, and $s:I\to\{1,-1\}$ with $\sum_is_i=\pm1$. Slots are $(K\sqcup K)\times I$: a disk number in $K$, a kind (positive or negative) and a position in $I$. For $X\in U(K)$ the scalar mixer is the block-diagonal matrix $Q_X=\bigoplus_{i\in I}\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$, which exchanges the two kinds at each position. The sign coordinates place the first copy of $K\times I$ in the positive half at positions with $s_i=1$ and in the negative half otherwise, and the second copy oppositely. Let $T$ be a self-adjoint unitary on slots whose entries between two slots of the same copy vanish. Then there is $X\in U(K)$ with
--   $$
--   2|K|\le\mathrm{fix}(Q_XT),
--   $$
--   where $\mathrm{fix}$ is the dimension of the fixed space.
--
--   This is the fixed-space input to the phase bound at relator corners.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/Traversal.lean#L169-L194

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
attribute [local instance] OAI.KervaireTraversal.instDecidableEqSlots
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]

theorem OAI.KervaireTraversal.exists_mixer_for_exchange (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (T : Matrix (Slots I K) (Slots I K) ℂ)
    (hTs : star T = T) (hTu : T ∈ unitary (Matrix (Slots I K) (Slots I K) ℂ))
    (h₀ : ∀ i j, T (coordinates s (.inl i)) (coordinates s (.inl j)) = 0)
    (h₁ : ∀ i j, T (coordinates s (.inr i)) (coordinates s (.inr j)) = 0) :
    ∃ X : unitary (Matrix K K ℂ), 2 * Fintype.card K ≤ fixedDim (mixer (X : Matrix K K ℂ) * T) := by sorry
