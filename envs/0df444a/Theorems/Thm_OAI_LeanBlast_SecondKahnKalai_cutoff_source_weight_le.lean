-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_cutoff_source_weight_le
-- name    : OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:04:54.834284+00:00
-- url     : https://prove2.me/theorems/6efa4844-fa26-4b56-a2ec-386ee41ec270
-- title:
--   Cutoff bound on a single resampling transition weight
-- statement:
--   Let $X$ be a set, $B$ a finite index set, $\nu$ a probability vector on $B$ (weights $\nu(e)\ge 0$ with $\sum_{e\in B}\nu(e)=1$) and $(A_e)_{e\in B}$ finite subsets of $X$ (the labels). Fix a real number $p\ge 0$. For a finite set $Y\subseteq X$ let
--   $$
--   Z_p(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,p^{-|A_e|}
--   $$
--   be the resampling density, and for a finite set $W\subseteq X$ and $c,b\in B$ let
--   $$
--   K_W(c,b)=\nu(c)\cdot\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,p^{-|A_b|}}{Z_p(W\cup A_c)}
--   $$
--   be the weight of the source–target pair $(c,b)$ in the resampling step at $W$: the source $c$ is drawn from $\nu$, and the target $b$ is drawn with probability proportional to $\nu(b)p^{-|A_b|}$ among the labels contained in the observed set $W\cup A_c$.
--
--   Then for every $\delta>0$, every finite $W\subseteq X$ and all $c,b\in B$,
--   $$
--   \mathbf{1}\{\delta\le Z_p(W\cup A_c)\}\;K_W(c,b)\;\le\;\mathbf{1}\{A_b\setminus A_c\subseteq W\}\;\frac{\nu(c)\,\nu(b)\,p^{-|A_b|}}{\delta}.
--   $$
--
--   So once the density at the observed set is at least $\delta$, the transition weight exceeds the product weight $\nu(c)\nu(b)p^{-|A_b|}$ by at most the factor $\delta^{-1}$, and it vanishes unless $W$ contains the part of the target label lying outside the source label. Summed over sources and averaged over a $p$-random set $W$, this is the pointwise input of the outside-coordinate change of measure for the resampling transition.
--
--   **Formalization Note** The indicators are Lean `if … then … else 0` expressions and $p^{-k}$ is `(p⁻¹) ^ k`. Lean's conventions $x/0=0$ and $0^{-1}=0$ apply, so the case $p=0$ is included. The probability vector is a `FiniteLaw B`; no positivity of $\nu$ is assumed, and $X$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean#L95-L123

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem OAI.LeanBlast.SecondKahnKalai.cutoff_source_weight_le (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ) (W : Finset X) (c b : B) :
    (if δ ≤ resamplingZ ν A p (resamplingY A W c)
      then resamplingWeight ν A p W (c, b) else 0) ≤
      if A b \ A c ⊆ W then δ⁻¹ * ν.weight c * ν.weight b * (p⁻¹) ^ (A b).card
      else 0 := by sorry
