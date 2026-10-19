-- Prove2me | Theorems.Thm_OAI_KervaireBoundary_exists_band_mixer
-- name    : OAI.KervaireBoundary.exists_band_mixer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:51:24.84972+00:00
-- url     : https://prove2.me/theorems/f877b6ba-46f1-48f8-8956-b2c2b35a6828
-- title:
--   A scalar mixer for a rotated band involution
-- statement:
--   Let $I$ be finite, $K$ finite and nonempty, and $s:I\to\{1,-1\}$ with $\sum_is_i=\pm1$. Slots are $(K\sqcup K)\times I$: a disk number in $K$, a kind (positive or negative) and a position in $I$. The traversal sign of a slot $(k,i)$ is $s_i$ on a positive disk and $-s_i$ on a negative disk. Let $\theta$ be an involution of the slots that reverses traversal signs, and $\gamma$ a real function on slots with $\gamma(\theta d)=-\gamma(d)$. Let $T$ be the weighted permutation matrix with entry $e^{2\pi i\gamma(d)}$ at $(\theta d,d)$, and $Q_X=\bigoplus_{i\in I}\begin{pmatrix}0&X^*\\X&0\end{pmatrix}$ the scalar mixer. Then there is $X\in U(K)$ with
--   $$
--   2|K|\le\mathrm{fix}(Q_XT),
--   $$
--   where $\mathrm{fix}$ is the dimension of the fixed space.
--
--   The angles $\gamma$ are later chosen to prescribe the phases around the boundary cycles of a diagram.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean#L198-L229

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
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow

open OAI OAI.KervaireBoundary
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
open Matrix KervaireMatrix KervaireRegular KervaireSpectral KervaireMixing KervaireTraversal
open scoped Classical
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

theorem OAI.KervaireBoundary.exists_band_mixer [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (γ : Slot I K → ℝ) (hγ : ∀ d, γ (θ d) = -γ d) :
    ∃ X : Matrix.unitaryGroup K ℂ, 2 * Fintype.card K ≤
      KervaireFixed.fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) *
        monomial θ (fun d ↦ scalarRotation (γ d))) := by sorry
