-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_large_fragment_bound
-- name    : OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:02.735181+00:00
-- url     : https://prove2.me/theorems/0fba4366-393e-41c4-a0e9-2bd10811b1ed
-- title:
--   Large-fragment failure of the resampling step is exponentially unlikely under spread
-- statement:
--   Let $X$ be a finite set, $B$ a finite index set, $\nu$ a probability vector on $B$ with $\nu(b)>0$ for every $b$, and $(A_b)_{b\in B}$ subsets of $X$. Let $0<\rho<1$, $a\ge 0$ and $m\in\mathbb{N}$, and assume:
--
--   1. $|A_b|\le m$ for every $b\in B$;
--   2. $\nu$ is $a$-spread for $A$: $\nu(\{b\in B: J\subseteq A_b\})\le a^{|J|}$ for every nonempty $J\subseteq X$;
--   3. $a/\rho\le e^{-50}$.
--
--   For $Y,W\subseteq X$ and $c,b\in B$ let
--   $$
--   Z_\rho(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,\rho^{-|A_e|},\qquad K_W(c,b)=\nu(c)\,\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,\rho^{-|A_b|}}{Z_\rho(W\cup A_c)} .
--   $$
--   $K_W$ is the probability distribution on $B\times B$ of one resampling step at $W$ (a source $c$ drawn from $\nu$, then a target $b$ drawn with probability proportional to $\nu(b)\rho^{-|A_b|}$ among the labels contained in $W\cup A_c$), and $K_W(E)=\sum_{(c,b)\in E}K_W(c,b)$ for $E\subseteq B\times B$. Let $\mathbb{E}_\rho[g]=\sum_{W\subseteq X}\rho^{|W|}(1-\rho)^{|X\setminus W|}g(W)$ be the expectation over a $\rho$-random subset $W\subseteq X$. Then
--   $$
--   \mathbb{E}_\rho\Big[K_W\big(\{(c,b):\ e^{-10m}\le Z_\rho(W\cup A_c)\ \text{and}\ |A_b\setminus W|>\lfloor m/2\rfloor\}\big)\Big]\;\le\;e^{10m}\,2^m\,e^{-25m}.
--   $$
--
--   This bounds the large-fragment failure mode of a resampling step, in which the observed set has density at least $e^{-10m}$ but the retained fragment $A_b\setminus W$ of the target label is more than half the capacity $m$. Together with the small-density bound it yields the exponential bound on local failure of the resampling transition.
--
--   **Formalization Note** The left side is `bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob …)`. The fragment condition is the natural-number inequality `m / 2 < (A b \ W).card` (floor division), equivalent to $2|A_b\setminus W|>m$; spread is `IsSpread ν A a`. The right side equals $2^m e^{-15m}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean#L163-L225

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

theorem OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hsize : ∀ b, (A b).card ≤ m) (hspread : IsSpread ν A a)
    (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => Real.exp (-10 * (m : ℝ)) ≤
          resamplingZ ν A ρ (resamplingY A W cb.1) ∧
        m / 2 < (A cb.2 \ W).card)) ≤
      Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by sorry
