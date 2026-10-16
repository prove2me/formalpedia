-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_small_density_bound
-- name    : OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:09:41.877976+00:00
-- url     : https://prove2.me/theorems/1f55557d-bcb2-4e0c-9bca-236495a120f0
-- title:
--   The resampling density is below a cutoff $\tau$ with probability at most $\tau$
-- statement:
--   Let $X$ be a finite set, $B$ a finite index set, $\nu$ a probability vector on $B$ with $\nu(b)>0$ for every $b$, and $(A_b)_{b\in B}$ subsets of $X$. Let $0<\rho<1$. For $Y,W\subseteq X$ and $c,b\in B$ let
--   $$
--   Z_\rho(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,\rho^{-|A_e|},\qquad K_W(c,b)=\nu(c)\,\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,\rho^{-|A_b|}}{Z_\rho(W\cup A_c)} ;
--   $$
--   $K_W$ is the probability distribution on $B\times B$ of one resampling step at $W$ (a source $c$ drawn from $\nu$, then a target $b$ drawn with probability proportional to $\nu(b)\rho^{-|A_b|}$ among the labels contained in the observed set $W\cup A_c$), and $K_W(E)=\sum_{(c,b)\in E}K_W(c,b)$. Let $\mathbb{E}_\rho[g]=\sum_{W\subseteq X}\rho^{|W|}(1-\rho)^{|X\setminus W|}g(W)$ be the expectation over a $\rho$-random subset $W\subseteq X$. Then for every $\tau\ge 0$,
--   $$
--   \mathbb{E}_\rho\Big[K_W\big(\{(c,b):\ Z_\rho(W\cup A_c)<\tau\}\big)\Big]\;\le\;\tau .
--   $$
--
--   The observed set $Y=W\cup A_c$, with $W$ $\rho$-random and $c$ drawn from $\nu$, has density exactly $Z_\rho$ with respect to the $\rho$-Bernoulli law, so the probability that this density falls below $\tau$ is at most $\tau$. With $\tau=e^{-10m}$ this controls the small-density failure mode of a resampling step.
--
--   **Formalization Note** The left side is `bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob (fun cb => resamplingZ ν A ρ (resamplingY A W cb.1) < τ))`, where `resamplingY A W c` is $W\cup A_c$; positivity of $\nu$ and $\rho>0$ make `resamplingLaw` a probability law.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean#L227-L244

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

theorem OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ τ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 ≤ τ) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => resamplingZ ν A ρ (resamplingY A W cb.1) < τ)) ≤ τ := by sorry
