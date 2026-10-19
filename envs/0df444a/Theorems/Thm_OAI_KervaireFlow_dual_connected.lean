-- Prove2me | Theorems.Thm_OAI_KervaireFlow_dual_connected
-- name    : OAI.KervaireFlow.dual_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:50:18.724132+00:00
-- url     : https://prove2.me/theorems/db6a890d-667c-4335-b3fd-dfca81e6fea2
-- title:
--   Connectivity passes to the dual graph
-- statement:
--   Let $b:D\to Z$ assign to each dart of a finite set $D$ a boundary label, and let $\theta$ be an involution of $D$. The dual graph on $Z$ has a directed edge from $x$ to $y$ whenever $b(d)=x$ and $b(\theta d)=y$ for some dart $d$. Assume $b$ is surjective, $\sigma$ is a permutation of $D$ with $b(\sigma(\theta d))=b(d)$ for all $d$, and any two darts are joined by a chain of steps $d\mapsto\sigma d$ or $d\mapsto\theta d$. Then every vertex reaches every other vertex in the dual graph:
--   $$
--   x\to^{*}y\qquad\text{for all }x,y\in Z .
--   $$
--
--   Changing the disk successor $\sigma$ to the boundary successor thus does not change connectivity of the dual graph.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/BoundaryFlow.lean#L153-L172

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
variable {D Z : Type*}

theorem OAI.KervaireFlow.dual_connected (b : D → Z) (hb : Function.Surjective b)
    (σ θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (hcycle : ∀ d, b (σ (θ d)) = b d)
    (hconn : ∀ d e, Relation.ReflTransGen (fun d e => e = σ d ∨ e = θ d) d e) :
    ∀ x y, Relation.ReflTransGen (Adj b θ) x y := by sorry
