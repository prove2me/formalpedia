-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalGeometry_exists_disjoint_balls
-- name    : OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:49:09.16682+00:00
-- url     : https://prove2.me/theorems/8e457620-fe6c-4c52-a3d5-64667a3dc4a3
-- title:
--   Finitely many distinct points have disjoint balls
-- statement:
--   For finitely many pairwise distinct points $z_j$ of a metric space there is $r>0$ such that the balls are pairwise disjoint:
--   $$
--   B(z_j,r)\cap B(z_k,r)=\varnothing\quad(j\ne k).
--   $$
--
--   Such radii are used for the cutoffs around exceptional points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLipschitz.lean#L160-L185

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalGeometry
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem OAI.LipschitzCounterexample.LocalGeometry.exists_disjoint_balls (z : I → M) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ Pairwise (fun j k => Disjoint (Metric.ball (z j) r) (Metric.ball (z k) r)) := by sorry
