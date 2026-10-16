-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_ProbabilityTree_CoverState_exists_advance_of_halved
-- name    : OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:26.68505+00:00
-- url     : https://prove2.me/theorems/58912168-9de6-4b2a-8ce4-b24c69d988ad
-- title:
--   Halving step: a halved tree that recovers the current one yields a cover state of smaller rank
-- statement:
--   Fix a ground set $X$, a probability tree $T_0$ on $X$ of some depth $k$ (the *original* tree), and a real number $\sigma$. The statement uses the following notions.
--
--   **Probability trees.** A probability tree of depth $0$ is a single leaf. A probability tree of depth $n+1$ consists of a root carrying a nonempty finite set $B$ of branches, a probability law $\mu$ on $B$ with $\mu(b)>0$ for every $b\in B$, a finite label $A_b\subseteq X$ on each branch $b$, and a probability tree $T_b$ of depth $n$ below each branch. The root is at level $0$, the roots of the subtrees $T_b$ are at level $1$, and so on. A *full path* $P$ is a sequence of branch choices from the root down to a leaf (different branch choices give different paths even when their labels agree), and $\bigcup P$ denotes the union of the labels along $P$. For a probability tree $T$:
--
--   - $T$ is *disjoint* if at every node each branch label $A_b$ is disjoint from all labels occurring in the subtree $T_b$;
--   - $T$ *has capacities* $c:\mathbb{N}\to\mathbb{N}$ if every branch leaving a node of level $i$ carries a label with at most $c(i)$ elements;
--   - $T$ *has spread* $\alpha:\mathbb{N}\to\mathbb{R}$ if at every node of level $i$, with law $\mu$ and labels $(A_b)_{b\in B}$, one has $\mu(\{b\in B: J\subseteq A_b\})\le\alpha(i)^{|J|}$ for every nonempty finite $J\subseteq X$;
--   - a probability tree $S$ of any depth *recovers* $T$ *modulo* a finite set $W\subseteq X$ if for every full path $Q$ of $S$ there is a full path $P$ of $T$ with $\bigcup P\subseteq W\cup\bigcup Q$.
--
--   **Cover states.** For $\ell\in\mathbb{N}$ put $r_\sigma(\ell)=4\sigma\prod_{j=1}^{\ell}(1-e^{-j})$ (the *reserve* at capacity $\ell$), and let $s(\ell)=\lfloor\log_2\ell\rfloor+1$ for $\ell\ge1$ and $s(0)=1$; for $\ell\ge1$, $s(\ell)$ is the number of halvings $\ell\mapsto\lfloor\ell/2\rfloor$ needed to reach $0$. A *cover state* for $(T_0,\sigma)$ is a quadruple $\Sigma=(d,S,c,Y)$ consisting of a depth $d\in\mathbb{N}$, a probability tree $S$ of depth $d$, a capacity sequence $c:\mathbb{N}\to\mathbb{N}$ and a finite set $Y\subseteq X$ of already seen elements, such that $S$ is disjoint, $S$ has capacities $c$, $S$ has spread $i\mapsto r_\sigma(c(i))$, $c(i)>0$ for all $i<d$, $16\,c(i)\le c(i+1)$ whenever $i+1<d$, and $S$ recovers $T_0$ modulo $Y$. Its *rank* is $\operatorname{rk}\Sigma=0$ if $d=0$ and $\operatorname{rk}\Sigma=s(c(d-1))$ if $d\ge1$. For a finite $W\subseteq X$, a cover state $\Sigma'=(d',S',c',Y')$ *advances* $\Sigma$ *on* $W$ if $\operatorname{rk}\Sigma'<\operatorname{rk}\Sigma$ and $Y'=Y\cup W$.
--
--   **Theorem.** Let $\Sigma=(d,S,c,Y)$ be a cover state for $(T_0,\sigma)$ with $d\neq0$, and let $W\subseteq X$ be finite. Let $U$ be a probability tree of the same depth $d$ such that
--
--   1. $U$ is disjoint,
--   2. $U$ has capacities $i\mapsto\lfloor c(i)/2\rfloor$,
--   3. $U$ has spread $i\mapsto r_\sigma(\lfloor c(i)/2\rfloor)$,
--   4. $U$ recovers $S$ modulo $W$.
--
--   Then some cover state for $(T_0,\sigma)$ advances $\Sigma$ on $W$: there is a cover state $\Sigma'=(d',S',c',Y')$ for $(T_0,\sigma)$ with
--
--   $$
--   \operatorname{rk}\Sigma'<\operatorname{rk}\Sigma\qquad\text{and}\qquad Y'=Y\cup W.
--   $$
--
--   In the iterative covering of a spread probability tree by random sets, each round draws a set $W$ and tries to replace the current tree by a reduced tree whose capacities are halved. This theorem is the deterministic bookkeeping step of that iteration: any halved tree that keeps disjointness and the reserve spread and still recovers the current tree modulo $W$ gives rise to a new cover state that has absorbed $W$ into its seen set and has strictly smaller rank, the rank being the number of halvings still available to the last capacity. Since the rank is a natural number, it can decrease only finitely often, which is what bounds the number of successful rounds.
--
--   **Formalization Note** Cover states are the structure `ProbabilityTree.CoverState original σ` (fields `depth`, `tree`, `capacity`, `seen` together with the six invariants); the rank is `CoverState.rank`, advancing is `CoverState.Advances`, recovery is `ProbabilityTree.Recovers`, $r_\sigma$ is `capacityReserve σ` and $s$ is `successesNeeded`, defined through `Nat.log2`, which is why $s(0)=1$. Halving is natural-number division. The ground type only needs decidable equality, and $\sigma$ is an arbitrary real number in this statement. Branch laws are `FiniteLaw`s (nonnegative real weights of total mass one), and positivity of all weights is part of the tree datatype `ProbabilityTree X d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean#L280-L328

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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.ProbabilityTree OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState
open Classical
variable {X : Type} [DecidableEq X]
variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

theorem OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_halved (state : CoverState original σ) (W : Finset X)
    (hdepth : state.depth ≠ 0) (U : ProbabilityTree X state.depth)
    (hdisjoint : U.IsDisjoint)
    (hcapacity : U.HasCapacities (fun i => state.capacity i / 2))
    (hspread : U.HasSpread (fun i => capacityReserve σ (state.capacity i / 2)))
    (hrecovery : Recovers state.tree U W) :
    ∃ next, state.Advances W next := by sorry
