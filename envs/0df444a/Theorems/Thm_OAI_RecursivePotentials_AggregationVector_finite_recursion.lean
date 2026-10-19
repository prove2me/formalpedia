-- Prove2me | Theorems.Thm_OAI_RecursivePotentials_AggregationVector_finite_recursion
-- name    : OAI.RecursivePotentials.AggregationVector.finite_recursion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T08:25:50.165692+00:00
-- url     : https://prove2.me/theorems/8356c319-08ec-4c48-9d68-94db61d3b584
-- title:
--   Root-sum potentials of finitely supported vectors satisfy the $\ell^p$ child recursion at every node
-- statement:
--   Let $I$ be an arbitrary index set carrying a rooted tree $T$: a root $r$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth function $\operatorname{dep}:I\to\mathbb{N}$ with $\operatorname{dep}(r)=0$ and $\operatorname{dep}(\pi(s))<\operatorname{dep}(s)$ for $s\neq r$. Nodes may have infinitely many children; the children of $s$ are the nodes $c\neq r$ with $\pi(c)=s$, and $C(s)$ is their set. Fix a real exponent $p\ge1$, and for real numbers $t,\alpha,\beta$ write
--   $$
--   \Lambda(t,\alpha,\beta)=\bigl(\max(\alpha,\,t+\beta),\ \max(\beta,\,\alpha-t)\bigr).
--   $$
--   For a finitely supported $v:I\to\mathbb{R}$, its head $H(v)$ is the finite set consisting of $r$ and all ancestors of points of the support of $v$ (each point counting as its own ancestor). The potentials $P(v),Q(v):I\to[0,\infty)$ are obtained by computing on the finite tree $H(v)$, from the deepest nodes upwards, the recursion $\bigl(P_s(v),Q_s(v)\bigr)=\Lambda\bigl(v_s,\ (\sum_c P_c(v)^p)^{1/p},\ (\sum_c Q_c(v)^p)^{1/p}\bigr)$, with $c$ ranging over the children of $s$ inside $H(v)$, and by setting $P_s(v)=Q_s(v)=0$ for $s\notin H(v)$. For a node $s$ let $\mathbf P^{(s)}(v),\mathbf Q^{(s)}(v)\in\ell^p(I)$ be the vectors whose coordinate at $c$ is $P_c(v)$, respectively $Q_c(v)$, when $c\in C(s)$, and $0$ otherwise.
--
--   **Theorem.** For every node $s\in I$ and every finitely supported $v:I\to\mathbb{R}$,
--   $$
--   \bigl(P_s(v),\,Q_s(v)\bigr)=\Lambda\Bigl(v_s,\ \bigl\|\mathbf P^{(s)}(v)\bigr\|_{\ell^p},\ \bigl\|\mathbf Q^{(s)}(v)\bigr\|_{\ell^p}\Bigr),
--   $$
--   that is, $P_s(v)=\max\bigl(\|\mathbf P^{(s)}(v)\|_{\ell^p},\,v_s+\|\mathbf Q^{(s)}(v)\|_{\ell^p}\bigr)$ and $Q_s(v)=\max\bigl(\|\mathbf Q^{(s)}(v)\|_{\ell^p},\,\|\mathbf P^{(s)}(v)\|_{\ell^p}-v_s\bigr)$, where $\|\mathbf P^{(s)}(v)\|_{\ell^p}=\bigl(\sum_{c\in C(s)}P_c(v)^p\bigr)^{1/p}$ has only finitely many nonzero terms.
--
--   The potentials were defined by a computation on the finite head of $v$; the theorem shows that they satisfy the same local recursion over the whole tree, at nodes inside and outside the head, with the child aggregation taken over all children as an $\ell^p(I)$ norm. Because $P_s$, $Q_s$ and the child vectors depend continuously on $v$ for the root-sum norm $P_r+Q_r$, the identity passes to the completion of the finitely supported vectors, which is the first step in characterizing the potentials of the completed $\ell^p$-model as the solution of this recursion.
--
--   **Formalization Note** $\Lambda$ is `leastPair`, the potentials are `VariableTree.P T e v` and `VariableTree.Q T e v`, and $\mathbf P^{(s)}(v)$, $\mathbf Q^{(s)}(v)$ are `childP T e s v` and `childQ T e s v`, elements of `lp (fun _ => ℝ) (ENNReal.ofReal e.val)`. The exponent is a `ChildExponent` $e$ (a real number at least $1$); no strict inequality $e>1$ and no bound on the height is assumed. Lean's aggregation uses $|P_c|^p$, which equals $P_c^p$ since potentials are nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableStability.lean#L336-L382

import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableStability

open OAI OAI.RecursivePotentials OAI.RecursivePotentials.AggregationVector
universe uIndex uSpace uOther uDomain uTarget uFiber
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
open Filter Topology TopologicalSpace
open scoped ENNReal
open FiniteRootedTree
variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

theorem OAI.RecursivePotentials.AggregationVector.finite_recursion (s : ι) (v : AggregationVector T e) :
    (VariableTree.P T e v s,VariableTree.Q T e v s) =
      leastPair (v s) ‖childP T e s v‖ ‖childQ T e s v‖ := by sorry
