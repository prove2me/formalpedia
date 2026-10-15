-- Prove2me | Theorems.Thm_OAI_DiscreteFree_opposing_scalar_extension
-- name    : OAI.DiscreteFree.opposing_scalar_extension
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T09:54:07.362219+00:00
-- url     : https://prove2.me/theorems/d15c8ee2-8bdc-4ea6-9f21-8e0a72ab1259
-- title:
--   A bounded $1$-Lipschitz function equal to $b$ on one set and to $-c$ on another
-- statement:
--   Let $(N,d)$ be a metric space, let $P,Q\subseteq N$ be subsets, let $L\ge0$, and let $b,c\colon N\to\mathbb{R}$ be $1$-Lipschitz functions with
--   $$
--   0\le b(z)\le L\quad\text{and}\quad 0\le c(z)\le L\qquad\text{for all } z\in N .
--   $$
--   Assume the separation condition: whenever $j\in P$, $k\in Q$ and $d(j,k)<2L$, both $b(j)=0$ and $c(k)=0$.
--
--   **Theorem.** There is a function $f\colon N\to\mathbb{R}$ such that
--   $$
--   |f(z)-f(z')|\le d(z,z')\ \ (z,z'\in N),\qquad |f(z)|\le L\ \ (z\in N),\qquad f=b\ \text{on } P,\qquad f=-c\ \text{on } Q .
--   $$
--
--   The sets $P$ and $Q$ need not be disjoint; on $P\cap Q$ the hypotheses force $b=c=0$. The result produces the test functions of the block obstruction: $b$ and $c$ are Lipschitz bumps of height $L$ centered at the labels of two adjacent vertices, $P$ and $Q$ are the non-exceptional parts of a finite support set for the two vertices, and the resulting $f$ is a norm-one Lipschitz test that pairs positively with one vertex and negatively with the other.
--
--   **Formalization Note** The Lipschitz conditions are `LipschitzWith 1`, the agreements are `Set.EqOn f b P` and `Set.EqOn f (fun z => -c z) Q`, and the bounds $0\le b,c\le L$ are assumed on all of $N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/SignedTests.lean#L117-L168

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests

open OAI OAI.DiscreteFree
open scoped BigOperators ENNReal
variable {N : Type*} [MetricSpace N]

theorem OAI.DiscreteFree.opposing_scalar_extension (P Q : Set N) (b c : N → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbLip : LipschitzWith 1 b) (hcLip : LipschitzWith 1 c)
    (hb : ∀ j, 0 ≤ b j ∧ b j ≤ L) (hc : ∀ j, 0 ≤ c j ∧ c j ≤ L)
    (hcross : ∀ j ∈ P, ∀ k ∈ Q, dist j k < 2 * L → b j = 0 ∧ c k = 0) :
    ∃ f : N → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      Set.EqOn f b P ∧ Set.EqOn f (fun z => -c z) Q := by sorry
