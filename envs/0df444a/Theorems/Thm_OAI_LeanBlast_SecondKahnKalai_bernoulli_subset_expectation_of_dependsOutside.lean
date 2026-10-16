-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulli_subset_expectation_of_dependsOutside
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:06:15.5034+00:00
-- url     : https://prove2.me/theorems/88ad01ac-2d04-4dac-9ade-259a78a1ce2f
-- title:
--   Containment of ignored coordinates factors out of a Bernoulli expectation
-- statement:
--   Let $X$ be a finite set and let $p\neq 0$ be a real number. For $f:2^X\to\mathbb{R}$ write
--   $$
--   \mathbb{E}_p[f]=\sum_{W\subseteq X}p^{|W|}(1-p)^{|X\setminus W|}\,f(W);
--   $$
--   for $0<p\le 1$ this is the expectation of $f(W)$ when $W$ is a $p$-random subset of $X$ (every element is included independently with probability $p$). Say that $f$ *ignores* a set $A\subseteq X$ if $f(W)=f(V)$ whenever $W\setminus A=V\setminus A$, that is, $f(W)$ depends only on the coordinates of $W$ outside $A$.
--
--   Let $S\subseteq A\subseteq X$ and suppose that $f$ ignores $A$. Then
--   $$
--   \mathbb{E}_p\big[\mathbf{1}\{S\subseteq W\}\,f(W)\big]=p^{|S|}\,\mathbb{E}_p[f].
--   $$
--
--   For $0<p\le 1$ this says that the containment event $\{S\subseteq W\}$, of probability $p^{|S|}$, is independent of every observable that ignores the coordinates of a set $A\supseteq S$; the observable may depend on the remaining coordinates of the same random set in an arbitrary way. It is the tool used to integrate the cutoff bound for the resampling transition against an observable that ignores the target label.
--
--   **Formalization Note** The identity is proved for every nonzero real $p$, with $\mathbb{E}_p[f]$ the weighted sum `bernoulliExpectation p f`; the hypothesis on $f$ is `DependsOutside A f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean#L127-L149

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
variable [Fintype X]

theorem OAI.LeanBlast.SecondKahnKalai.bernoulli_subset_expectation_of_dependsOutside
    {p : ℝ} (hp : p ≠ 0) (A S : Finset X) (f : Finset X → ℝ)
    (hf : DependsOutside A f) (hSA : S ⊆ A) :
    bernoulliExpectation p (fun W => if S ⊆ W then f W else 0) =
      p ^ S.card * bernoulliExpectation p f := by sorry
