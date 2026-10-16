-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_copy_incidence_identity
-- name    : OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:40:17.337004+00:00
-- url     : https://prove2.me/theorems/1c300b6f-c929-4e63-88b2-6dc6bbd4ac94
-- title:
--   Double-counting identity for nested orbit copies under a finite group action
-- statement:
--   Let $G$ be a finite group acting on a set $X$. For a finite set $F\subseteq X$ and $g\in G$ write $gF=\{gx: x\in F\}$. The distinct sets of the form $gF$ are the *copies* of $F$; let $\mathcal{C}(F)=\{gF: g\in G\}$ be the set of copies (each set counted once, no matter how many group elements produce it). Put $N(F)=|\mathcal{C}(F)|$, and for finite $I,F\subseteq X$ define
--
--   - $\operatorname{cont}(I,F)=\#\{J\in\mathcal{C}(I): F\subseteq J\}$, the number of copies of $I$ that contain the fixed set $F$;
--   - $\operatorname{int}(I,F)=\#\{U\in\mathcal{C}(F): U\subseteq I\}$, the number of copies of $F$ that lie inside the fixed set $I$.
--
--   **Theorem.** For all finite subsets $I,F\subseteq X$,
--   $$
--   N(F)\cdot\operatorname{cont}(I,F)=N(I)\cdot\operatorname{int}(I,F).
--   $$
--
--   Both sides count the pairs $(U,J)$ in which $U$ is a copy of $F$, $J$ is a copy of $I$, and $U\subseteq J$. Dividing by $N(F)N(I)$, the identity says that the probability that a uniformly random copy of $I$ contains $F$ equals the number of copies of $F$ inside $I$ divided by the total number of copies of $F$. In the graph-threshold application ($X$ the edge set of $K_n$, $G$ the symmetric group permuting the vertices) this converts containment probabilities for random copies into counts of subgraph copies, which can then be compared with expected copy numbers.
--
--   **Formalization Note** No finiteness of $X$ is assumed, and $I$, $F$ are arbitrary `Finset`s (possibly empty). $N$, $\operatorname{cont}$ and $\operatorname{int}$ are `orbitCount G`, `containingCopyCount G I F` and `internalCopyCount G I F`; they are natural numbers and the identity is an equality in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/CopyOrbits.lean#L166-L188

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators Pointwise
universe u v
variable (G : Type u) [Group G] [Fintype G]
variable {X : Type v} [DecidableEq X] [MulAction G X]

theorem OAI.LeanBlast.SecondKahnKalai.copy_incidence_identity (I F : Finset X) :
    orbitCount G F * containingCopyCount G I F =
      orbitCount G I * internalCopyCount G I F := by sorry
