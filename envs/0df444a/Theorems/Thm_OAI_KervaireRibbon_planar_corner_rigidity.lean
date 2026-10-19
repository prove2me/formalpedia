-- Prove2me | Theorems.Thm_OAI_KervaireRibbon_planar_corner_rigidity
-- name    : OAI.KervaireRibbon.planar_corner_rigidity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:54:10.642126+00:00
-- url     : https://prove2.me/theorems/76286d7b-e58a-480a-8ac6-0b499b5644ab
-- title:
--   Corner rigidity for planar diagrams on slots
-- statement:
--   Let $A$ be a group, $I,K$ nonempty finite sets, $\rho$ a cyclic permutation of $I$, $a:I\to A$, and $s:I\to\{1,-1\}$ with $\sum_is_i=\pm1$. Slots are $(K\sqcup K)\times I$: a disk number in $K$, a kind (positive or negative) and a position in $I$. The traversal sign of a slot $(k,i)$ is $s_i$ on a positive disk and $-s_i$ on a negative disk. The disk successor $\sigma$ on slots moves positive slots by $\rho$ and negative slots by $\rho^{-1}$ in the position. The slot labels are $\ell(k^+,i)=a_i^{-1}$ and $\ell(k^-,i)=a_{\rho^{-1}i}$. Let $\theta$ be an involution reversing traversal signs such that $(\sigma,\theta)$ is connected and planar. Let $u$ be potentials on slots with $\ell(d)^{-1}=u(\theta d)\,u(\sigma d)^{-1}$ at every slot $d\ne p$. Then also
--   $$
--   \ell(p)^{-1}=u(\theta p)\,u(\sigma p)^{-1}.
--   $$
--
--   In a connected planar diagram built from $2|K|$ copies of the relator, a corner condition that holds at all corners but one holds at the last.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/RibbonRigidity.lean#L181-L241

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

open OAI OAI.KervaireRibbon
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
open Equiv Equiv.Perm KervaireCycle KervaireMixing KervaireTraversal KervaireBoundary
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A]

theorem OAI.KervaireRibbon.planar_corner_rigidity [Nonempty I] [Nonempty K]
    (ρ : Perm I) (hρ : ∀ i j, ρ.SameCycle i j) (a : I → A)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = - traversalSign s d)
    (hconn : components (successor ρ) θ = ⊤) (hp : planar (successor ρ) θ)
    (u : Slot I K → A) (p : Slot I K)
    (hu : ∀ d, d ≠ p → (labels ρ a d)⁻¹ = u (θ d) * (u (successor ρ d))⁻¹) :
    (labels ρ a p)⁻¹ = u (θ p) * (u (successor ρ p))⁻¹ := by sorry
