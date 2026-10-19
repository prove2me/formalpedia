-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_finite_witness_of_block_detection
-- name    : OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:37:02.659068+00:00
-- url     : https://prove2.me/theorems/c9ff8a8a-1f6d-47fc-800b-4c73b97c2bbf
-- title:
--   Block detection yields a leaf whose switch vector satisfies all its detectors
-- statement:
--   Let $K$ be a convex subset of a real normed space and consider an ordered tree with positive edge weights $w(c)$ summing to $1$ over each parent's children, path weights $\pi_k(v)$, and nonexpansive node maps $f_{k,v}:K\to K$, evaluated bottom-up by $\mathrm{collapse}(H)(p)=f_{k,p}(\sum_{\mathrm{par}(c)=p}w(c)H(c))$. In the switching experiment at level $N$ with leaf labels $y$ and common point $b$, $\rho(t)$ is the root value when leaves $s<t$ carry $y_s$ and the others carry $b$; the states before and after the block of a node $v$ are $\rho(\mathrm{hi}(v))$ and $\rho(\mathrm{lo}(v))$, and $u_s=\pi_N(s)^{-1}(\rho(s+1)-\rho(s))$. Assume $\operatorname{diam}K\le1$, all differences of $K$ lie in a subspace $Y$, and functionals $f_{k,v}$ have $\|f_{k,v}\|\le1$. Suppose numbers $e_v$ with $\sum_ve_v\le\frac1{128}$ satisfy, for every nonroot node $v$ of depth at most $N$,
--   $$
--   f_v\bigl(\rho(\mathrm{hi}(v))-\rho(\mathrm{lo}(v))\bigr)\ge\pi(v)-5e_v .
--   $$
--   Then some leaf $s$ has $u_s\in Y$, $\|u_s\|\le1$, and $f_{i,\mathrm{anc}_i(s)}(u_s)\ge\frac12$ for all $0<i\le N$.
--
--   So every finite depth has a feasible node whose witness lies in the unit ball of $Y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/FiniteWitness.lean#L43-L96

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem OAI.ReflexiveFixedPoints.TreeEvaluation.finite_witness_of_block_detection
    (N : ℕ) (y : T.Node N → K) (b : K)
    (Y : Submodule ℝ X) (hY : ∀ a c : K, (a : X) - c ∈ Y)
    (hdiam : ∀ a c : K, ‖(a : X) - c‖ ≤ 1)
    (f : (k : ℕ) → T.Node k → X →L[ℝ] ℝ)
    (hf : ∀ k v, ‖f k v‖ ≤ 1)
    (e : T.TruncationNode N → ℝ)
    (he : (∑ v, e v) ≤ (1 : ℝ) / 128)
    (hblock : ∀ v : T.TruncationNode N,
      W.pathWeight (v.1.val + 1) v.2 - 5 * e v ≤
        f (v.1.val + 1) v.2
          ((E.beforeBlock v.levelBound y b v.2 : X) -
            E.afterBlock v.levelBound y b v.2)) :
    ∃ s : T.Node N,
      E.switchVector N y b s ∈ Y ∧ ‖E.switchVector N y b s‖ ≤ 1 ∧
        ∀ i (hi : i ≤ N), 0 < i →
          (1 : ℝ) / 2 ≤ f i (T.ancestorLE hi s) (E.switchVector N y b s) := by sorry
