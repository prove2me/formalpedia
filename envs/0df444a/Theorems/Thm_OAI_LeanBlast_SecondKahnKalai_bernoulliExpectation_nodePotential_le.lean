-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_nodePotential_le
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:11:27.069829+00:00
-- url     : https://prove2.me/theorems/3774025a-d294-4519-93a9-3dcc76064b3d
-- title:
--   Expectation recursion for the node potential
-- statement:
--   Let $X$ and $B$ be finite sets, $p\in\mathbb{R}$, $m\in\mathbb{N}$, and let $\nu$ be a probability vector on $B$ (weights $\nu(b)\ge 0$ summing to $1$). For $g:2^X\to\mathbb{R}$ write
--   $$
--   \mathbb{E}_p[g]=\sum_{W\subseteq X}p^{|W|}(1-p)^{|X\setminus W|}\,g(W),
--   $$
--   which for $0\le p\le 1$ is the expectation of $g(W)$ for a $p$-random subset $W\subseteq X$. For a real number $x$ and families $s=(s_b)_{b\in B}$, $u=(u_b)_{b\in B}$ of real numbers let $\Phi_m(x,s,u)=e^{m}\big(x+\sum_{b\in B}s_b u_b\big)$ be the node potential.
--
--   Let $\varphi:2^X\to\mathbb{R}$ and $t_b,\psi_b:2^X\to\mathbb{R}$ ($b\in B$) be arbitrary functions such that
--
--   1. $\mathbb{E}_p[\varphi]\le e^{-9m}$;
--   2. $\mathbb{E}_p[t_b\,\psi_b]\le e^{11m}\,\nu(b)\,\mathbb{E}_p[\psi_b]$ for every $b\in B$.
--
--   Then
--   $$
--   \mathbb{E}_p\Big[\Phi_m\big(\varphi(W),\,(t_b(W))_{b},\,(\psi_b(W))_{b}\big)\Big]\;\le\;e^{-8m}+e^{12m}\sum_{b\in B}\nu(b)\,\mathbb{E}_p[\psi_b].
--   $$
--
--   This is one step of the expectation recursion for the bad-node potential of a probability tree: hypothesis 1 is supplied by the local failure bound and hypothesis 2, for each child separately, by the outside-coordinate change of measure. The products $t_b\psi_b$ are never factored, so no independence between a node's transition masses and its children's potentials is needed. Iterating over the levels of the tree gives a deterministic envelope for the expected potential.
--
--   **Formalization Note** $\mathbb{E}_p$ is `bernoulliExpectation p`, $\Phi_m$ is `nodePotential m` (a division by `Real.exp (-(m : ℝ))`), and the right-hand sum is `ν.expectation (fun b => bernoulliExpectation p (childPotential b))`. The statement holds for every real $p$; no sign conditions on the functions are assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean#L83-L120

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_nodePotential_le {X B : Type*} [Fintype X] [DecidableEq X]
    [Fintype B] (p : ℝ) (m : ℕ) (ν : FiniteLaw B) (failure : Finset X → ℝ)
    (target childPotential : B → Finset X → ℝ)
    (hfailure : bernoulliExpectation p failure ≤ Real.exp (-9 * (m : ℝ)))
    (hchild : ∀ b,
      bernoulliExpectation p (fun W => target b W * childPotential b W) ≤
        Real.exp (11 * (m : ℝ)) * ν.weight b * bernoulliExpectation p (childPotential b)) :
    bernoulliExpectation p (fun W => nodePotential m (failure W)
      (fun b => target b W) (fun b => childPotential b W)) ≤
      Real.exp (-8 * (m : ℝ)) + Real.exp (12 * (m : ℝ)) *
        ν.expectation (fun b => bernoulliExpectation p (childPotential b)) := by sorry
