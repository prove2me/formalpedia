-- Prove2me | Theorems.Thm_OAI_KervaireFlow_exists_flow
-- name    : OAI.KervaireFlow.exists_flow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:49:22.196627+00:00
-- url     : https://prove2.me/theorems/bacca106-15d4-4814-8879-261dd1e163c4
-- title:
--   Boundary phases with total zero come from antisymmetric flows
-- statement:
--   Let $b:D\to Z$ assign to each dart of a finite set $D$ a boundary label, and let $\theta$ be an involution of $D$. The dual graph on $Z$ has a directed edge from $x$ to $y$ whenever $b(d)=x$ and $b(\theta d)=y$ for some dart $d$. Suppose every vertex can reach every other vertex in the dual graph. Then for every $\eta:Z\to\mathbb R$ with $\sum_z\eta_z=0$ there is $\gamma:D\to\mathbb R$ with $\gamma(\theta d)=-\gamma(d)$ for all $d$ and
--   $$
--   \sum_{d:\,b(d)=z}\gamma(d)=\eta_z\qquad(z\in Z).
--   $$
--
--   So any boundary phases with total zero are realized by antisymmetric phases on the paired slots.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean#L128-L149

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

open OAI OAI.KervaireFlow
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
open scoped Classical
variable {D Z : Type*} [Fintype D] [Fintype Z]

theorem OAI.KervaireFlow.exists_flow (b : D → Z) (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hconn : ∀ x y, Relation.ReflTransGen (Adj b θ) x y)
    (root : Z) (η : Z → ℝ) (hη : ∑ z, η z = 0) :
    ∃ γ : D → ℝ, (∀ d, γ (θ d) = -γ d) ∧
      ∀ z, (∑ d, if b d = z then γ d else 0) = η z := by sorry
