-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_treePotential_dependsOnlyOn
-- name    : OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:12:46.149617+00:00
-- url     : https://prove2.me/theorems/69ca0a44-50a6-413b-8910-dc82f20295f8
-- title:
--   The tree potential depends only on the coordinates in the tree's support
-- statement:
--   Let $X$ be a set; all subsets $W,V,A_b$ of $X$ below are finite. A *probability tree* of depth $d$ over $X$ is defined recursively: a tree of depth $0$ is a leaf, and a tree of depth $d+1$ is a node consisting of a finite index set $B$, a probability vector $\nu$ on $B$ with $\nu(b)>0$ for all $b$, labels $A_b\subseteq X$ and subtrees $T_b$ of depth $d$ ($b\in B$). The *support* of a tree is the union of all its labels: $\operatorname{supp}(\text{leaf})=\emptyset$ and $\operatorname{supp}(T)=\bigcup_{b\in B}\big(A_b\cup\operatorname{supp}(T_b)\big)$ for a node $T$.
--
--   Fix $p\in\mathbb{R}$. At a node with data $(B,\nu,A)$, a capacity $k\in\mathbb{N}$ and a set $W$, let
--   $$
--   Z_p(Y)=\sum_{e\in B:\ A_e\subseteq Y}\nu(e)\,p^{-|A_e|},\qquad K_W(c,b)=\nu(c)\,\frac{\mathbf{1}\{A_b\subseteq W\cup A_c\}\,\nu(b)\,p^{-|A_b|}}{Z_p(W\cup A_c)}
--   $$
--   be the resampling density and transition weights. Call $(c,b)$ a local success if $e^{-10k}\le Z_p(W\cup A_c)$ and $|A_b\setminus W|\le\lfloor k/2\rfloor$, and a local failure otherwise. Let $F_k(W)$ be the total $K_W$-weight of local failures and $S_{k,b}(W)=\sum_{c:\,(c,b)\ \text{success}}K_W(c,b)$ the successful mass into $b$. For a capacity sequence $m=(m_0,m_1,\dots)$ of natural numbers, the *tree potential* is defined by $\Psi_{p,m}(W,\text{leaf})=0$ and, for a node $T$,
--   $$
--   \Psi_{p,m}(W,T)=e^{m_0}\Big(F_{m_0}(W)+\sum_{b\in B}S_{m_0,b}(W)\,\Psi_{p,m'}(W,T_b)\Big),\qquad m'=(m_1,m_2,\dots).
--   $$
--
--   Then for every $p\in\mathbb{R}$, every capacity sequence $m$, every depth $d$, every probability tree $T$ of depth $d$ and all finite $W,V\subseteq X$,
--   $$
--   W\cap\operatorname{supp}(T)=V\cap\operatorname{supp}(T)\ \Longrightarrow\ \Psi_{p,m}(W,T)=\Psi_{p,m}(V,T).
--   $$
--
--   All nodes of the tree are evaluated on the same random set $W$, and this locality statement is what makes the outside-coordinate change of measure applicable: when the labels along each path are disjoint, the potential of the subtree below an arc ignores the coordinates of that arc's label.
--
--   **Formalization Note** The conclusion is `DependsOnlyOn T.support (fun W => treePotential p m W T)`, where `DependsOnlyOn S f` means `∀ W V, W ∩ S = V ∩ S → f W = f V`. Trees are the inductive type `ProbabilityTree X d`; the potential uses `nodePotential (m 0)`, `localFailureMass` and `successfulTargetMass`, with the capacity condition in natural-number floor division and Lean's convention $x/0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreePotential.lean#L188-L208

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical
variable {X : Type} [Fintype X] [DecidableEq X]

omit [Fintype X] in
theorem OAI.LeanBlast.SecondKahnKalai.treePotential_dependsOnlyOn (p : ℝ) (m : ℕ → ℕ) {d : ℕ}
    (T : ProbabilityTree X d) : DependsOnlyOn T.support (fun W => treePotential p m W T) := by sorry
