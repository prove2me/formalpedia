-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_resamplingZ
-- name    : OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_resamplingZ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:07:59.083992+00:00
-- url     : https://prove2.me/theorems/9c001dba-508c-4c87-8ce4-ab005946c766
-- title:
--   Mixture expansion of the resampling density under a Bernoulli expectation
-- statement:
--   Let $X$ be a finite set, $B$ a finite index set, $\nu$ a probability vector on $B$ (weights $\nu(c)\ge 0$ summing to $1$), $(A_c)_{c\in B}$ subsets of $X$, and $\rho\in\mathbb{R}$. Define the resampling density
--   $$
--   Z_\rho(Y)=\sum_{c\in B:\ A_c\subseteq Y}\nu(c)\,\rho^{-|A_c|}\qquad(Y\subseteq X),
--   $$
--   and for $F:2^X\to\mathbb{R}$ the Bernoulli expectation $\mathbb{E}_\rho[F]=\sum_{Y\subseteq X}\rho^{|Y|}(1-\rho)^{|X\setminus Y|}F(Y)$. Then for every $F:2^X\to\mathbb{R}$,
--   $$
--   \mathbb{E}_\rho\big[Z_\rho(Y)\,F(Y)\big]=\sum_{c\in B}\nu(c)\;\mathbb{E}_\rho\Big[\mathbf{1}\{A_c\subseteq Y\}\,\frac{F(Y)}{\rho^{|A_c|}}\Big].
--   $$
--
--   For $0<\rho\le 1$ the inner expectation on the right is the expectation of $F$ under the $\rho$-Bernoulli law conditioned on the event $\{A_c\subseteq Y\}$, which has probability $\rho^{|A_c|}$. The identity therefore expresses the measure with density $Z_\rho$ relative to the Bernoulli law as the $\nu$-mixture of these conditioned laws; combined with the union-fixed formula it shows that the observed set $W\cup A_c$ of a resampling step ($W$ $\rho$-random, $c$ drawn from $\nu$) has density $Z_\rho$. It is a purely algebraic identity: no normalization, positivity or range condition is assumed.
--
--   **Formalization Note** The identity holds for every real $\rho$ under Lean's conventions $0^{-1}=0$ and $x/0=0$. In Lean, $Z_\rho$ is `resamplingZ ν A ρ`, written with `(ρ⁻¹) ^ (A c).card`, while the right-hand side divides by `ρ ^ (A c).card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/ResamplingDensity.lean#L53-L70

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
variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

theorem OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_resamplingZ (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) =
      ∑ c, ν.weight c * bernoulliExpectation ρ
        (fun Y => if A c ⊆ Y then F Y / ρ ^ (A c).card else 0) := by sorry
