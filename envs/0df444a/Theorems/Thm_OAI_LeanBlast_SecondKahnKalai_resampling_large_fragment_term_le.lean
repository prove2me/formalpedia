-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_large_fragment_term_le
-- name    : OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:08:36.402497+00:00
-- url     : https://prove2.me/theorems/b36e26ec-fa79-4ad5-bc61-4f0a3875ad32
-- title:
--   Large retained fragments force a large source–target overlap
-- statement:
--   Let $X$ be a set, $B$ a finite index set, $\nu$ a probability vector on $B$ (weights $\nu(e)\ge 0$ summing to $1$), $(A_e)_{e\in B}$ finite subsets of $X$, $\rho>0$ and $m\in\mathbb{N}$. For finite $Y,W\subseteq X$ and $c,b\in B$ let
--   $$
--   Z_\rho(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,\rho^{-|A_e|},\qquad K_W(c,b)=\nu(c)\,\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,\rho^{-|A_b|}}{Z_\rho(W\cup A_c)}
--   $$
--   be the resampling density and the weight of the source–target pair $(c,b)$ in the resampling step at $W$; the set $A_b\setminus W$ is the retained fragment of the target label. Then for every finite $W\subseteq X$ and all $c,b\in B$,
--   $$
--   \mathbf{1}\Big\{e^{-10m}\le Z_\rho(W\cup A_c)\ \text{and}\ |A_b\setminus W|>\lfloor m/2\rfloor\Big\}\,K_W(c,b)\;\le\;\mathbf{1}\Big\{2\,|A_c\cap A_b|>m\ \text{and}\ A_b\setminus A_c\subseteq W\Big\}\,e^{10m}\,\nu(c)\,\nu(b)\,\rho^{-|A_b|}.
--   $$
--   Here $|A_b\setminus W|>\lfloor m/2\rfloor$ is equivalent to $2|A_b\setminus W|>m$.
--
--   In words: a transition whose observed set has density at least $e^{-10m}$ and whose retained fragment exceeds half the capacity $m$ can only occur when the source and target labels share more than $m/2$ elements and $W$ contains the rest of the target label, and its weight is then at most $e^{10m}$ times the product weight $\nu(c)\nu(b)\rho^{-|A_b|}$. Averaging over $W$ and summing over pairs, this reduces the large-fragment failure probability to an intersection tail controlled by spread.
--
--   **Formalization Note** The fragment condition is the natural-number inequality `m / 2 < (A b \ W).card` with floor division. The indicators are `if … then … else 0` expressions and $\rho^{-k}$ is `(ρ⁻¹) ^ k`. The set $X$ need not be finite and $\nu$ need not have full support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean#L58-L112

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
open Finset
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

omit [Fintype X] in
theorem OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_term_le (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 < ρ) (m : ℕ) (W : Finset X) (c b : B) :
    (if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
          m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) ≤
      if m < 2 * (A c ∩ A b).card ∧ A b \ A c ⊆ W then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card
      else 0 := by sorry
