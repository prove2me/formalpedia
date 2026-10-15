-- Prove2me | Theorems.Thm_OAI_SegmentLenses_mem_atomicBody_of_norm_le_one
-- name    : OAI.SegmentLenses.mem_atomicBody_of_norm_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T21:07:13.244067+00:00
-- url     : https://prove2.me/theorems/8dc1765b-a30a-44e3-b612-99b0e4dd70b0
-- title:
--   Dual functionals supported on a finite ancestral set with norm at most one lie in the atomic body
-- statement:
--   Let $V$ be partially ordered by an ancestry relation $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$"), such that every interval $[a,b]=\{v\in V:\ a\le v\le b\}$ is finite and the order is a *tree order*: $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. Suppose $V$ carries a segment system whose segments are exactly the intervals $[a,b]$ with $a\le b$, and call a finite set of pairwise disjoint segments a *segment family*. For a finitely supported $u:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $u(S)=\sum_{v\in S}u(v)$. The family seminorm of a segment family $\mathcal F$ is $\|u\|_{\mathcal F}=\big(\sum_{S\in\mathcal F}u(S)^2\big)^{1/2}$, and the segment norm is $\|u\|_{\mathrm{seg}}=\sup_{\mathcal F}\|u\|_{\mathcal F}$, the supremum over all segment families.
--
--   Let $J_V$ be the completion of the finitely supported functions under $\|\cdot\|_{\mathrm{seg}}$. Finitely supported functions are regarded as elements of $J_V$, and $e_v=\delta_v$ are the unit vectors. Let $J_V^{*}$ be the continuous dual of $J_V$ with the operator norm, let $e_v^{*}\in J_V^{*}$ be the coordinate functional extending $u\mapsto u(v)$, and put $\sigma_S=\sum_{v\in S}e_v^{*}$ for finite $S\subseteq V$, so that $\sigma_S(u)=u(S)$. For finite $H\subseteq V$ the head and tail of $x\in J_V^{*}$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^{*}$ and $Q_Hx=x-P_Hx$. A finite set $H\subseteq V$ is *ancestral* if $b\in H$ and $a\le b$ imply $a\in H$.
--
--   Fix a finite set $K\subseteq V$. A *local family* of $K$ is a segment family all of whose members are subsets of $K$; there are only finitely many. *Local coefficients* on $K$ are tuples $c=(c_{\mathcal F})$ indexed by the local families, with $c_{\mathcal F}\in\mathbb{R}^{\mathcal F}$ carrying the Euclidean norm $\|\cdot\|_2$. Their value and budget are
--   $$
--   \Lambda_Kc=\sum_{\mathcal F}\sum_{S\in\mathcal F}c_{\mathcal F}(S)\,\sigma_S,\qquad\beta_K(c)=\sum_{\mathcal F}\|c_{\mathcal F}\|_2 ,
--   $$
--   and the atomic body of radius $R$ is $\mathcal A_K(R)=\{\Lambda_Kc:\ \beta_K(c)\le R\}\subseteq J_V^{*}$.
--
--   Let $K\subseteq V$ be finite and ancestral, and let $z\in J_V^{*}$ satisfy $P_Kz=z$ and $\|z\|\le1$. Then $z\in\mathcal A_K(1)$, i.e. there are local coefficients $c$ on $K$ with
--   $$
--   z=\sum_{\mathcal F}\sum_{S\in\mathcal F}c_{\mathcal F}(S)\,\sigma_S\qquad\text{and}\qquad\sum_{\mathcal F}\|c_{\mathcal F}\|_2\le1 .
--   $$
--
--   This is an atomic decomposition of the dual unit ball over a finite ancestral set. Call $\Lambda_{\mathcal F}d=\sum_{S\in\mathcal F}d_S\sigma_S$ with $\|d\|_2\le1$ an atom. The theorem says that every functional with $P_Kz=z$ and $\|z\|\le1$ is a combination of atoms from local families of $K$ with total weight at most $1$. It turns the dual norm into a statement about finite averages of segment representations of energy at most $1$, from which the midpoint argument builds finite laws of representations.
--
--   **Formalization Note** `atomicBody K 1` is the image of `{c | coefficientBudget K c ≤ 1}` under the linear map `localValue K`. The coefficient vectors live in `EuclideanSpace ℝ F.sets`, and `head K z = z` says $z=\sum_{v\in K}z(e_v)\,e_v^{*}$. Decidable equality, `LocallyFiniteOrder`, `TreeOrder` and `IntervalSegments` (segments are exactly the intervals) are instance arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/AtomicBalls.lean#L219-L250

import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls

open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem OAI.SegmentLenses.mem_atomicBody_of_norm_le_one {K : Finset V} (hK : Ancestral (· ≤ ·) K)
    (z : FullDual V) (hz : head K z = z) (hn : ‖z‖ ≤ 1) :
    z ∈ atomicBody K 1 := by sorry
