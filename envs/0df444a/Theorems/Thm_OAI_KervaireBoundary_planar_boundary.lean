-- Prove2me | Theorems.Thm_OAI_KervaireBoundary_planar_boundary
-- name    : OAI.KervaireBoundary.planar_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:52:36.871367+00:00
-- url     : https://prove2.me/theorems/5732a3b5-172a-48db-b7ad-6ff8b1a638c8
-- title:
--   Boundary holonomies of a planar relator diagram
-- statement:
--   Let $A$ be a group, $I,K$ nonempty finite sets, $\rho$ a permutation of $I$, $a:I\to A$, and $s:I\to\{1,-1\}$ with $\sum_is_i=\pm1$. Slots are $(K\sqcup K)\times I$: a disk number in $K$, a kind (positive or negative) and a position in $I$. The traversal sign of a slot $(k,i)$ is $s_i$ on a positive disk and $-s_i$ on a negative disk. The disk successor $\sigma$ on slots moves positive slots by $\rho$ and negative slots by $\rho^{-1}$ in the position. The slot labels are $\ell(k^+,i)=a_i^{-1}$ and $\ell(k^-,i)=a_{\rho^{-1}i}$. Let $\theta$ be an involution of the slots reversing traversal signs, such that any slot reaches any other by steps $\sigma$ and $\theta$. Index the cycles of $\sigma\theta$ by a finite set $Z$, with coordinates $e(z,i)$ for $i\in\mathbb Z/(n_z+1)$, and assume $|Z|+2|K|=2+|I||K|$. Let
--   $$
--   c_z=\ell(\theta e(z,n_z))\cdots\ell(\theta e(z,1))\,\ell(\theta e(z,0)).
--   $$
--   If $c_z=1$ for every $z\ne z_0$, then $c_{z_0}=1$.
--
--   The equation on $|Z|$ is Euler's formula for a connected planar diagram. The statement is the analytic step: trivial holonomy around all but one boundary cycle forces it around the last.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean#L266-L325

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
open KervaireCycle KervaireSpectral KervaireMatrix KervaireRegular KervaireMixing KervaireTraversal
open scoped Classical
attribute [local instance] OAI.KervaireBoundary.instDecidableEqSlot_1
variable {I K Z A : Type*} [Fintype I] [Fintype K] [Fintype Z] [Group A]
  [Nonempty I] [Nonempty K]

theorem OAI.KervaireBoundary.planar_boundary
    (ρ : Equiv.Perm I) (a : I → A) (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (θ : Equiv.Perm (Slot I K)) (hθ : ∀ d, θ (θ d) = d)
    (hop : ∀ d, traversalSign s (θ d) = -traversalSign s d)
    (n : Z → ℕ) (e : (Σ z, Fin (n z+1)) ≃ Slot I K)
    (he : ∀ z i, ((successor (K := K) ρ : Equiv.Perm (Slot I K)) * θ) (e ⟨z,i⟩) = e ⟨z,finRotate (n z+1) i⟩)
    (hconn : ∀ d f, Relation.ReflTransGen (fun d f => f = successor ρ d ∨ f = θ d) d f)
    (hEuler : Fintype.card Z + 2*Fintype.card K = 2+Fintype.card I*Fintype.card K)
    (z₀ : Z)
    (hc : ∀ z, z ≠ z₀ → orbitWeight (finRotate (n z+1))
      (fun i ↦ labels ρ a (θ (e ⟨z,i⟩))) (n z+1) 0 = 1) :
    orbitWeight (finRotate (n z₀+1))
      (fun i ↦ labels ρ a (θ (e ⟨z₀,i⟩))) (n z₀+1) 0 = 1 := by sorry
