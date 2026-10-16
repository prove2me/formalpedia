-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_outside_change_of_measure_moment
-- name    : OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:06:58.773693+00:00
-- url     : https://prove2.me/theorems/7c515d45-1557-4f68-a1ca-ab0051dbc6d7
-- title:
--   Outside-coordinate change of measure for the resampling transition
-- statement:
--   Let $X$ be a finite set, $B$ a finite index set, $\nu$ a probability vector on $B$ (weights $\nu(e)\ge 0$ summing to $1$) and $(A_e)_{e\in B}$ subsets of $X$. Fix $0<p\le 1$ and $\delta>0$. For $Y,W\subseteq X$ and $c,b\in B$ let
--   $$
--   Z_p(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,p^{-|A_e|},\qquad K_W(c,b)=\nu(c)\,\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,p^{-|A_b|}}{Z_p(W\cup A_c)}
--   $$
--   be the resampling density and the weight of the source–target pair $(c,b)$ in the resampling step at $W$. The *cutoff target mass* of $b$ is
--   $$
--   M_\delta(W,b)=\sum_{c\in B}\mathbf{1}\{\delta\le Z_p(W\cup A_c)\}\,K_W(c,b),
--   $$
--   the weight of the transitions that end at $b$ and whose observed set $W\cup A_c$ has density at least $\delta$. Write $\mathbb{E}_p[g]=\sum_{W\subseteq X}p^{|W|}(1-p)^{|X\setminus W|}g(W)$ for the expectation over a $p$-random subset $W\subseteq X$.
--
--   Let $b\in B$ and let $f:2^X\to\mathbb{R}$ satisfy $f(W)\ge 0$ for all $W$ and ignore the target label $A_b$, i.e. $f(W)=f(V)$ whenever $W\setminus A_b=V\setminus A_b$. Then
--   $$
--   \mathbb{E}_p\big[M_\delta(W,b)\,f(W)\big]\;\le\;\frac{\nu(b)}{\delta}\;\mathbb{E}_p[f]\;\sum_{c\in B}\nu(c)\,p^{-|A_c\cap A_b|}.
--   $$
--
--   Compared with the product value $\nu(b)\,\mathbb{E}_p[f]$, the loss is the factor $\delta^{-1}$ times the intersection moment $\sum_{c}\nu(c)p^{-|A_c\cap A_b|}$, which a spread hypothesis on $\nu$ controls afterwards. The observable $f$ may depend on the same random set $W$ in an arbitrary way outside $A_b$; no independence is assumed. This change of measure is what allows the expectation of a tree potential to be bounded one child at a time.
--
--   **Formalization Note** $M_\delta(W,b)$ is `cutoffTargetMass ν A p δ W b`, the moment on the right is `ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card)`, and the locality hypothesis is `DependsOutside (A b) f`. Lean's convention $x/0=0$ enters only through the definition of $K_W$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/OutsideChangeOfMeasure.lean#L151-L210

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

theorem OAI.LeanBlast.SecondKahnKalai.outside_change_of_measure_moment (ν : FiniteLaw B) (A : B → Finset X)
    {p δ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hδ : 0 < δ)
    (b : B) (f : Finset X → ℝ) (hf : ∀ W, 0 ≤ f W)
    (hloc : DependsOutside (A b) f) :
    bernoulliExpectation p (fun W => cutoffTargetMass ν A p δ W b * f W) ≤
      δ⁻¹ * ν.weight b * bernoulliExpectation p f *
        ν.expectation (fun c => (p⁻¹) ^ (A c ∩ A b).card) := by sorry
