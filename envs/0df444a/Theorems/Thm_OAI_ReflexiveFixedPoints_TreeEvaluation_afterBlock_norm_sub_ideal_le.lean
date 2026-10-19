-- Prove2me | Theorems.Thm_OAI_ReflexiveFixedPoints_TreeEvaluation_afterBlock_norm_sub_ideal_le
-- name    : OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T16:32:56.955058+00:00
-- url     : https://prove2.me/theorems/ca49d549-a2ff-440d-8180-d071d2493f20
-- title:
--   The state after a block switch is close to the ideal cutoff
-- statement:
--   Let $K$ be a convex subset of a real normed space and consider an ordered tree with positive edge weights $w(c)$ summing to $1$ over each parent's children, path weights $\pi_k(v)$, and nonexpansive node maps $f_{k,v}:K\to K$, evaluated bottom-up by $\mathrm{collapse}(H)(p)=f_{k,p}(\sum_{\mathrm{par}(c)=p}w(c)H(c))$. In the switching experiment at level $N$ with leaf labels $y$ and common point $b$, $\rho(t)$ is the root value when leaves $s<t$ carry $y_s$ and the others carry $b$; the states before and after the block of a node $v$ are $\rho(\mathrm{hi}(v))$ and $\rho(\mathrm{lo}(v))$, and $u_s=\pi_N(s)^{-1}(\rho(s+1)-\rho(s))$. Take labels $y_s=f_{N,s}(x)$. Suppose child averages of labels return near $x$ within $\tau_d$ at levels $d<N$, with $\sum_{d=k}^{N-1}\tau_d\le e$, and the terminal defect $\sum_{d<N}\sum_s\|f_{d,s}(b)-b\|\le e$. Then for a node $v$ at level $k\le N$,
--   $$
--   \bigl\|\rho(\mathrm{lo}(v))-\mathrm{ev}_k(\mathrm{cut}_v)\bigr\|\le e ,
--   $$
--   where the ideal cutoff $\mathrm{cut}_v$ is $f_{k,u}(x)$ for $u<v$ and $b$ for $u\ge v$.
--
--   After the block of $v$ has switched, the root is within $e$ of the ideal cutoff state.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Nonexpansive/BlockEstimates.lean#L50-L75

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

open OAI OAI.ReflexiveFixedPoints OAI.ReflexiveFixedPoints.TreeEvaluation
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {T : OrderedTree} {W : WeightedTree T} {K : Set X}
variable (E : TreeEvaluation W K)

theorem OAI.ReflexiveFixedPoints.TreeEvaluation.afterBlock_norm_sub_ideal_le
    (x b : K) (τ : ℕ → ℝ) {k N : ℕ} (h : k ≤ N) (v : T.Node k)
    (haverage : ∀ d, d < N → ∀ p : T.Node d,
      ‖(E.childAverage d (fun c => E.map (d + 1) c x) p : X) - x‖ ≤ τ d)
    {e : ℝ} (htail : (∑ d ∈ Finset.Ico k N, τ d) ≤ e)
    (hterminal : E.terminalDefect N b ≤ e) :
    ‖(E.afterBlock h (fun s => E.map N s x) b v : X) -
      E.evaluate k (E.idealCutoff k x b v)‖ ≤ e := by sorry
