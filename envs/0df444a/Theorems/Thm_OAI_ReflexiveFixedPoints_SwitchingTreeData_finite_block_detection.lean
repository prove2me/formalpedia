-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_SwitchingTreeData_finite_block_detection
-- name    : OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:45:50.868557+00:00
-- url     : https://prove2.me/theorems/7b9e318b-ca4a-4536-8a72-a6c2c0393456
-- title:
--   Block detection in the switching experiment
-- statement:
--   Let $A$ be switching tree data for normalized minimal data $(K,T)$: a weighted tree of generated nonexpansive maps $f_v$ with anchor $a$, node labels $f_v(a)$, budgets $\beta_v=2^{-(\ell(v)+9)}$ for injective labels $\ell$, functionals $\varphi_v$ with $\|\varphi_v\|\le1$, terminal sequence $b_j=R_{j+1}(a)$, tolerances $\tau_k=2^{-(k+1)}m_k$ from the cumulative budget minima $m_k$, and prediction limits $\Lambda_v$ with $\varphi_v(f_v(a)-\Lambda_v)\ge1-\beta_v$. Fix $N$ and a terminal index $j$ satisfying the conclusion of the finite terminal choice. Run the switching experiment at level $N$ with the node labels as leaf labels and $b_j$ as common point. Then every nonroot node $v$ of depth at most $N$ satisfies
--   $$
--   \varphi_v\bigl(\rho(\mathrm{hi}(v))-\rho(\mathrm{lo}(v))\bigr)\ge\pi(v)-5\beta_v .
--   $$
--
--   Each detector sees the full path weight of its block in the switching increments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/TreeFiniteWitness.lean#L96-L125

import Mathlib
import Definitions.Def_ReflexiveFixedPoints
import Definitions.Def_OAI_Analysis_Nonexpansive_Model
import Definitions.Def_OAI_Analysis_Nonexpansive_Basic
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakCompactness
import Definitions.Def_OAI_Analysis_Nonexpansive_ScalarNormalization
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakMetric
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedTree
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeFrontier
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCompact
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionOutputs
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeBudget
import Definitions.Def_OAI_Analysis_Nonexpansive_Resolvents
import Definitions.Def_OAI_Analysis_Nonexpansive_GeneratedMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMaps
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateRecords
import Definitions.Def_OAI_Analysis_Nonexpansive_Diametral
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactDetector
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateThreshold
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePreparation
import Definitions.Def_OAI_Analysis_Nonexpansive_SequentialHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveRun
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveConvexPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_AdaptiveParentReturn
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakSelfMap
import Definitions.Def_OAI_Analysis_Nonexpansive_PointwiseWeakApproximation
import Definitions.Def_OAI_Analysis_Nonexpansive_CompactMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_TailMapSemigroup
import Definitions.Def_OAI_Analysis_Nonexpansive_WeakNestedConvexHull
import Definitions.Def_OAI_Analysis_Nonexpansive_Anchor
import Definitions.Def_OAI_Analysis_Nonexpansive_AnchorAdaptiveSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateSelection
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedGroupConcat
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierFromGroups
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevel
import Definitions.Def_OAI_Analysis_Nonexpansive_FrontierTower
import Definitions.Def_OAI_Analysis_Nonexpansive_TerminalSequence
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateStages
import Definitions.Def_OAI_Analysis_Nonexpansive_GlobalCandidateOrdinals
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLabels
import Definitions.Def_OAI_Analysis_Nonexpansive_ParentReturnHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_FinitePrefixEmbedding
import Definitions.Def_OAI_Analysis_Nonexpansive_ListRunPrefix
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLevelHistory
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedger
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateLedgerJoin
import Definitions.Def_OAI_Analysis_Nonexpansive_PrefixPredictionReindex
import Definitions.Def_OAI_Analysis_Nonexpansive_PredictionCutoff
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeEvaluation
import Definitions.Def_OAI_Analysis_Nonexpansive_SubtreeErrors
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockBefore
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingStates
import Definitions.Def_OAI_Analysis_Nonexpansive_OrderedTreeIntervals
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingBlocks
import Definitions.Def_OAI_Analysis_Nonexpansive_TransmittedSubtreeErrors
import Definitions.Def_OAI_Analysis_Nonexpansive_BlockEstimates
import Definitions.Def_OAI_Analysis_Nonexpansive_LedgerPredictionLimits
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidatePredictions
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateAncestors
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateDetectors
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_CandidateTreeTolerance
import Definitions.Def_OAI_Analysis_Nonexpansive_SwitchingTreeData
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeProducer
import Definitions.Def_OAI_Analysis_Nonexpansive_WeightedDeficit
import Definitions.Def_OAI_Analysis_Nonexpansive_FiniteWitness
import Definitions.Def_OAI_Analysis_Nonexpansive_FeasibleBranch
import Definitions.Def_OAI_Analysis_Nonexpansive_TreeFiniteWitness

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.SwitchingTreeData
open Filter
open scoped Topology BigOperators Pointwise
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {D : NormalizedMinimalData (X := X)}
variable (A : SwitchingTreeData D)

theorem OAI.ReflexiveFixedPoints.SwitchingTreeData.finite_block_detection (N j : ℕ)
    (hdet : ∀ v : A.tree.TruncationNode N,
      1 - 2 * A.budget (v.1.val + 1) v.2 ≤
        A.functionalAt (v.1.val + 1) v.2
          ((A.nodeLabel (v.1.val + 1) v.2 : X) -
            A.evaluation.evaluate (v.1.val + 1)
              (A.evaluation.idealCutoff (v.1.val + 1) A.anchor (A.terminal j) v.2)))
    (hD : A.evaluation.terminalDefect (N + 1) (A.terminal j) ≤
      A.tree.cumulativeMinimum (OrderedTree.retainedBudget A.label) N)
    (v : A.tree.TruncationNode N) :
    A.weights.pathWeight (v.1.val + 1) v.2 - 5 * A.budget (v.1.val + 1) v.2 ≤
      A.functionalAt (v.1.val + 1) v.2
        ((A.evaluation.beforeBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2 : X) -
          A.evaluation.afterBlock v.levelBound (A.nodeLabel N) (A.terminal j) v.2) := by sorry
