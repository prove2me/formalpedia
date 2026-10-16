-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_setHierarchy
-- name    : OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:32.380014+00:00
-- url     : https://prove2.me/theorems/76a15470-4561-413c-a816-3af0d9c0598f
-- title:
--   Existence of a hierarchy $\emptyset=A_0\subseteq\cdots\subseteq A_d=H$ with growth factor above $17$
-- statement:
--   Let $X$ be a set, $H\subseteq X$ a finite subset, and $R$ a binary relation on finite subsets of $X$; read $R(S,I)$ as "$S$ is an admissible predecessor of $I$". Assume that every nonempty subset of $H$ has a much smaller admissible predecessor inside it:
--   $$
--   \text{for every } I\subseteq H \text{ with } I\neq\emptyset \text{ there is } S\subseteq I \text{ with } 17|S|<|I| \text{ and } R(S,I).
--   $$
--
--   **Theorem.** Then there is a *hierarchy* for $R$ ending at $H$: a natural number $d$ (the depth) and finite sets $A_0,A_1,A_2,\ldots\subseteq X$ such that
--
--   1. $A_0=\emptyset$ and $A_d=H$;
--   2. $A_i\subseteq A_{i+1}$ for every $i<d$;
--   3. $17|A_i|<|A_{i+1}|$ for every $i<d$;
--   4. $R(A_i,A_{i+1})$ for every $i<d$.
--
--   Thus repeatedly passing to predecessors produces a chain $\emptyset=A_0\subseteq A_1\subseteq\cdots\subseteq A_d=H$ whose sizes grow by a factor larger than $17$ at each step; consequently $|H|\ge 17^{d-1}$ whenever $d\ge 1$, so the depth is logarithmic in $|H|$. In the threshold argument $R(S,I)$ says that $S$ is the maximizing predecessor of $I$, and the hierarchy is the skeleton along which a tree of copies of $H$ is built.
--
--   **Formalization Note** The conclusion is `Nonempty (SetHierarchy R H)`, a structure with fields `depth`, `stage : ℕ → Finset X` and the four properties above (`first`, `last`, `nested`, `sparse`, `selected`); the values of `stage` beyond `depth` are unconstrained. The hypothesis is required only for subsets of $H$, and $X$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean#L76-L134

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset

theorem OAI.LeanBlast.SecondKahnKalai.exists_setHierarchy {X : Type*} [DecidableEq X]
    (R : Finset X → Finset X → Prop) (H : Finset X)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I) :
    Nonempty (SetHierarchy R H) := by sorry
